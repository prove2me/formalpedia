-- Prove2me | solution 1 for FiniteEnergyPlane.loopAction_ccwLoop_eq_dlambdaEnergy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T21:28:51.561622+00:00
-- url     : https://prove2.me/submissions/69c6e94f-17c0-4f25-831b-2e166f9c97dd

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

variable {n : ℕ}

/-- The partner index `2i ↔ 2i+1`. -/
def pairIdx (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

theorem pairIdx_involutive : Function.Involutive (pairIdx (n := n)) := by
  intro k
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [pairIdx, h, h', dite_true, dite_false]
    ext; simp; omega

theorem j0_add (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring

theorem j0_smul (c : ℝ) (u : V n) : j0 (c • u) = c • j0 u := by
  funext k; simp only [j0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := j0_add, map_smul' := j0_smul }

@[simp] theorem j0L_apply (u : V n) : j0L u = j0 u := rfl

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply]

theorem omega0_antisymm (u v : V n) : omega0 u v = -omega0 v u := by
  have e := Equiv.sum_comp (Function.Involutive.toPerm _ (pairIdx_involutive (n := n)))
    (fun k => j0 u k * v k)
  simp only [omega0, dot]
  rw [← e, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.Involutive.coe_toPerm, pairIdx, j0]
  by_cases h : (k : ℕ) % 2 = 0
  · have h' : ¬ ((k : ℕ) + 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) + 1 - 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp
    rw [this]; ring
  · have h' : ((k : ℕ) - 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false, dite_true, dite_false]
    have : (⟨(k : ℕ) - 1 + 1, by have := k.2; omega⟩ : Fin (2 * (n + 1))) = k := by
      ext; simp; omega
    rw [this]; ring

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The boundary term of a smooth map `w` on the circle of radius `r`. -/
noncomputable def bdryTerm {n : ℕ} (w : ℂ → V n) (r : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
    omegaL (w (circleMap 0 r θ)) (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))

/-- Stokes on an annulus for `ω₀(∂ₛw, ∂ₜw)`. -/
theorem setIntegral_annulus_eq_bdryTerm {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ z in ball 0 b \ ball 0 a, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      bdryTerm w b - bdryTerm w a := by
  have hc : Continuous (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) := by
    have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
    simp_rw [← omegaL_apply]
    exact (omegaL.continuous₂).comp₂ (hd.clm_apply continuous_const)
      (hd.clm_apply continuous_const)
  rw [setIntegral_annulus_eq_integral_circleMap ha hab hc.continuousOn]
  have hS := integral_mul_integral_bilin_circleMap_eq (omegaL (n := n))
    (fun x y => by rw [omegaL_apply, omegaL_apply, omega0_antisymm]) isOpen_univ
    (hw.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top)) ha hab (fun _ _ _ => Set.mem_univ _) 0
  simp only [sub_zero, omegaL_apply] at hS
  simp only [smul_eq_mul, bdryTerm, omegaL_apply]
  exact hS

/-- The loop action of `u` on the circle of radius `R` is the boundary term of `proj ∘ u`. -/
theorem loopAction_eq_bdryTerm {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hw : ContDiff ℝ ∞ (fun z => proj H (u z))) (R : ℝ) :
    loopAction H u (ccwLoop R) = bdryTerm (fun z => proj H (u z)) R := by
  set w := fun z => proj H (u z) with hwdef
  have hcm : ∀ t : ℝ, ccwLoop R t = circleMap 0 R (2 * π * t) := by
    intro t; simp [ccwLoop, circleMap]
  have hloop : loopInS H u (ccwLoop R) = fun t => w (circleMap 0 R (2 * π * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hder : ∀ t : ℝ, deriv (loopInS H u (ccwLoop R)) t =
      (2 * π) • fderiv ℝ w (circleMap 0 R (2 * π * t)) (circleMap 0 R (2 * π * t) * Complex.I) := by
    intro t
    rw [hloop]
    have hh : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * π)
    have h1 := (hasDerivAt_circleMap 0 R (2 * π * t)).scomp t hh
    have h2 := ((hw.differentiable (by simp)) (circleMap 0 R (2 * π * t))).hasFDerivAt
    have := h2.comp_hasDerivAt t h1
    rw [show (fun t => w (circleMap 0 R (2 * π * t))) =
      w ∘ (circleMap 0 R ∘ fun t => 2 * π * t) from rfl, this.deriv, ← map_smul]
  unfold loopAction
  simp_rw [hder, hloop]
  simp only [liouville, map_smul, smul_eq_mul]
  have e : ∀ t : ℝ, omega0 (w (circleMap 0 R (2 * π * t)))
      ((2 * π) • fderiv ℝ w (circleMap 0 R (2 * π * t)) (circleMap 0 R (2 * π * t) * Complex.I)) / 2
      = π * (fun θ => omegaL (w (circleMap 0 R θ))
          (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I))) (2 * π * t) := by
    intro t
    simp only [← omegaL_apply, map_smul, smul_eq_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun θ => omegaL (w (circleMap 0 R θ))
      (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I))) (by positivity)]
  simp only [mul_zero, mul_one, smul_eq_mul, bdryTerm]
  rw [← mul_assoc]
  congr 1
  field_simp

theorem continuous_omega0_fderiv {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) :
    Continuous (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  simp_rw [← omegaL_apply]
  exact (omegaL.continuous₂).comp₂ (hd.clm_apply continuous_const)
    (hd.clm_apply continuous_const)

/-- Action of a circle equals the enclosed `dλ`-energy. -/
theorem loopAction_ccwLoop_eq_dlambdaEnergy_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (R : ℝ) (hR : 0 < R) :
    loopAction H u (ccwLoop R) = (dlambdaEnergy H (ball 0 R) u).toReal := by
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hw : ContDiff ℝ ∞ w :=
    contDiffOn_univ.1 (hprojs.comp hu.1 (fun z _ => hu.2.1 z (Set.mem_univ _)))
  set dens : ℂ → ℝ := fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) with hdensdef
  have hc : Continuous dens := continuous_omega0_fderiv w hw
  have hnn : ∀ z, 0 ≤ dens z := fun z =>
    (energyDensity_nonneg H hH J hJ Set.univ isOpen_univ u hu).2.1 z (Set.mem_univ _)
  have hD : (dlambdaEnergy H (ball 0 R) u).toReal = ∫ z in ball 0 R, dens z := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hc.aestronglyMeasurable]
    rfl
  rw [loopAction_eq_bdryTerm H u hw R, hD]
  have hint : ∀ r, IntegrableOn dens (ball 0 r) :=
    fun r => (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      ball_subset_closedBall
  have key : ∀ a, 0 < a → a ≤ R →
      (∫ z in ball 0 R, dens z) - bdryTerm w R = (∫ z in ball 0 a, dens z) - bdryTerm w a := by
    intro a ha haR
    have h1 := setIntegral_sdiff (μ := volume) measurableSet_ball (hint R) (ball_subset_ball haR)
    have h2 := setIntegral_annulus_eq_bdryTerm w hw ha haR
    rw [h2] at h1
    linarith
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hw.continuous_fderiv (by simp)).continuousOn
  have hM2n : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 (mem_closedBall_self zero_le_one))
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (mem_closedBall_self zero_le_one))
  set K := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hK
  have hKn : 0 ≤ K := norm_nonneg (omegaL (n := n))
  have hbd : ∀ a, 0 < a → a ≤ 1 → a ≤ R →
      |(∫ z in ball 0 R, dens z) - bdryTerm w R| ≤ K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a := by
    intro a ha ha1 haR
    rw [key a ha haR]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · have hvol : (volume : Measure ℂ).real (ball 0 a) = a ^ 2 * π := by
        simp [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal ha.le]
      rw [← hvol, ← Real.norm_eq_abs]
      refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top ?_
      intro z hz
      have hz1 : z ∈ closedBall (0 : ℂ) 1 :=
        ball_subset_closedBall (ball_subset_ball ha1 hz)
      have hb := hM2 z hz1
      simp only [hdensdef, ← omegaL_apply]
      refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
      have e1 : ‖fderiv ℝ w z 1‖ ≤ M2 :=
        ((fderiv ℝ w z).le_opNorm 1).trans (by simpa using hb)
      have e2 : ‖fderiv ℝ w z Complex.I‖ ≤ M2 :=
        ((fderiv ℝ w z).le_opNorm _).trans (by simpa using hb)
      exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hKn) e2 (norm_nonneg _) (mul_nonneg hKn hM2n)
    · rw [bdryTerm, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
      have hθ : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π), ‖omegaL (w (circleMap 0 a θ))
          (fderiv ℝ w (circleMap 0 a θ) (circleMap 0 a θ * Complex.I))‖ ≤ K * M1 * (M2 * a) := by
        intro θ _
        have hz1 : circleMap 0 a θ ∈ closedBall (0 : ℂ) 1 := by
          rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos ha]; exact ha1
        refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
        have e1 := hM1 _ hz1
        have e2 : ‖fderiv ℝ w (circleMap 0 a θ) (circleMap 0 a θ * Complex.I)‖ ≤ M2 * a := by
          refine ((fderiv ℝ w _).le_opNorm _).trans ?_
          rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos ha]
          exact mul_le_mul_of_nonneg_right (hM2 _ hz1) ha.le
        gcongr
      have := intervalIntegral.norm_integral_le_of_norm_le_const hθ
      rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
      nlinarith [this]
  have hlim : Tendsto (fun a : ℝ => K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a)
      (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (fun a : ℝ => K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a) := by
      fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      |(∫ z in ball 0 R, dens z) - bdryTerm w R| ≤ K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hR)] with a ha
    exact hbd a ha.1 (ha.2.le.trans (min_le_left _ _)) (ha.2.le.trans (min_le_right _ _))
  have h0 := ge_of_tendsto hlim hev
  have := abs_nonneg ((∫ z in ball 0 R, dens z) - bdryTerm w R)
  have hz : (∫ z in ball 0 R, dens z) - bdryTerm w R = 0 := abs_eq_zero.1 (le_antisymm h0 this)
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (R : ℝ) (hR : 0 < R) :
    loopAction H u (ccwLoop R) = (dlambdaEnergy H (ball 0 R) u).toReal :=
  loopAction_ccwLoop_eq_dlambdaEnergy_aux H hH J hJ u hu R hR
