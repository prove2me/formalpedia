-- Prove2me | solution 1 for FiniteEnergyPlane.energy_univ_eq_dlambdaEnergy_of_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:55:28.241112+00:00
-- url     : https://prove2.me/submissions/13300a6c-c7b3-4e6c-887c-58405e2fc152

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_loopAction_ccwLoop_eq_dlambdaEnergy
import Theorems.Thm_FiniteEnergyPlane_plane_asymptotics
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb



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
noncomputable def buBdry {n : ℕ} (w : ℂ → V n) (r : ℝ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π,
    omegaL (w (circleMap 0 r θ)) (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))

theorem bu_continuous_dens {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) :
    Continuous (fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I)) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  simp_rw [← omegaL_apply]
  exact (omegaL.continuous₂).comp₂ (hd.clm_apply continuous_const)
    (hd.clm_apply continuous_const)

theorem bu_continuous_bdry {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (r : ℝ) :
    Continuous (fun θ => omegaL (w (circleMap 0 r θ))
      (fderiv ℝ w (circleMap 0 r θ) (circleMap 0 r θ * Complex.I))) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  have hc : Continuous (circleMap 0 r) := continuous_circleMap 0 r
  exact (omegaL.continuous₂).comp₂ (hw.continuous.comp hc)
    ((hd.comp hc).clm_apply (hc.mul continuous_const))

theorem bu_annulus_eq {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ z in ball 0 b \ ball 0 a, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      buBdry w b - buBdry w a := by
  have hc := bu_continuous_dens w hw
  rw [setIntegral_annulus_eq_integral_circleMap ha hab hc.continuousOn]
  have hS := integral_mul_integral_bilin_circleMap_eq (omegaL (n := n))
    (fun x y => by rw [omegaL_apply, omegaL_apply, omega0_antisymm]) isOpen_univ
    (hw.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top)) ha hab (fun _ _ _ => Set.mem_univ _) 0
  simp only [sub_zero, omegaL_apply] at hS
  simp only [smul_eq_mul, buBdry, omegaL_apply]
  exact hS

/-- Stokes on a disc for `ω₀(∂ₛW, ∂ₜW)`, `W` smooth. -/
theorem bu_ball_eq {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (R : ℝ) (hR : 0 < R) :
    ∫ z in ball 0 R, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) = buBdry w R := by
  set dens : ℂ → ℝ := fun z => omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) with hdensdef
  have hc : Continuous dens := bu_continuous_dens w hw
  have hint : ∀ r, IntegrableOn dens (ball 0 r) :=
    fun r => (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      ball_subset_closedBall
  have key : ∀ a, 0 < a → a ≤ R →
      (∫ z in ball 0 R, dens z) - buBdry w R = (∫ z in ball 0 a, dens z) - buBdry w a := by
    intro a ha haR
    have h1 := setIntegral_sdiff (μ := volume) measurableSet_ball (hint R) (ball_subset_ball haR)
    have h2 := bu_annulus_eq w hw ha haR
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
      |(∫ z in ball 0 R, dens z) - buBdry w R| ≤
        K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a := by
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
    · rw [buBdry, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
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
      |(∫ z in ball 0 R, dens z) - buBdry w R| ≤
        K * M2 * M2 * (a ^ 2 * π) + π * K * M1 * M2 * a := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hR)] with a ha
    exact hbd a ha.1 (ha.2.le.trans (min_le_left _ _)) (ha.2.le.trans (min_le_right _ _))
  have h0 := ge_of_tendsto hlim hev
  have := abs_nonneg ((∫ z in ball 0 R, dens z) - buBdry w R)
  have hz : (∫ z in ball 0 R, dens z) - buBdry w R = 0 := abs_eq_zero.1 (le_antisymm h0 this)
  linarith

/-- The loop action integrand in terms of the `ω₀`-form on the circle. -/
theorem bu_liouville_loop {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hw : ContDiff ℝ ∞ (fun z => proj H (u z))) (R t : ℝ) :
    liouville (loopInS H u (ccwLoop R) t) (deriv (loopInS H u (ccwLoop R)) t) =
      π * omegaL (proj H (u (circleMap 0 R (2 * π * t))))
        (fderiv ℝ (fun z => proj H (u z)) (circleMap 0 R (2 * π * t))
          (circleMap 0 R (2 * π * t) * Complex.I)) := by
  set w := fun z => proj H (u z) with hwdef
  have hcm : ∀ t : ℝ, ccwLoop R t = circleMap 0 R (2 * π * t) := by
    intro t; simp [ccwLoop, circleMap]
  have hloop : loopInS H u (ccwLoop R) = fun t => w (circleMap 0 R (2 * π * t)) := by
    funext t; simp [loopInS, hwdef, hcm]
  have hh : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have h1 := (hasDerivAt_circleMap 0 R (2 * π * t)).scomp t hh
  have h2 := ((hw.differentiable (by simp)) (circleMap 0 R (2 * π * t))).hasFDerivAt
  have h3 := h2.comp_hasDerivAt t h1
  have hder : deriv (loopInS H u (ccwLoop R)) t =
      (2 * π) • fderiv ℝ w (circleMap 0 R (2 * π * t)) (circleMap 0 R (2 * π * t) * Complex.I) := by
    rw [hloop]
    rw [show (fun t => w (circleMap 0 R (2 * π * t))) =
      w ∘ (circleMap 0 R ∘ fun t => 2 * π * t) from rfl, h3.deriv, ← map_smul]
  rw [hder, hloop]
  simp only [liouville, ← omegaL_apply, map_smul, smul_eq_mul]
  ring

theorem bu_loopAction_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (hw : ContDiff ℝ ∞ (fun z => proj H (u z))) (R : ℝ) :
    loopAction H u (ccwLoop R) = buBdry (fun z => proj H (u z)) R := by
  unfold loopAction
  simp_rw [bu_liouville_loop H u hw R]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun θ => omegaL (proj H (u (circleMap 0 R θ)))
      (fderiv ℝ (fun z => proj H (u z)) (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)))
      (by positivity)]
  simp only [mul_zero, mul_one, smul_eq_mul, buBdry]
  rw [← mul_assoc]
  congr 1
  field_simp

/-- The energy density for `χ²` is the `ω₀`-density of `χ(a) • w`. -/
theorem bu_density_eq {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (z : ℂ) (ha : DifferentiableAt ℝ (fun z => aCoord H (u z)) z)
    (hw : DifferentiableAt ℝ (fun z => proj H (u z)) z) :
    omega0 (fderiv ℝ (fun z => χ (aCoord H (u z)) • proj H (u z)) z 1)
        (fderiv ℝ (fun z => χ (aCoord H (u z)) • proj H (u z)) z Complex.I) =
      energyDensity H (fun s => χ s ^ 2) u z := by
  have hca : HasFDerivAt (fun y => χ (aCoord H (u y)))
      (deriv χ (aCoord H (u z)) • fderiv ℝ (fun y => aCoord H (u y)) z) z :=
    (hχ (aCoord H (u z))).hasDerivAt.comp_hasFDerivAt z ha.hasFDerivAt
  have hW : HasFDerivAt (fun z => χ (aCoord H (u z)) • proj H (u z)) _ z :=
    hca.smul hw.hasFDerivAt
  rw [hW.fderiv]
  have hφ : deriv (fun s => χ s ^ 2) (aCoord H (u z)) =
      2 * χ (aCoord H (u z)) * deriv χ (aCoord H (u z)) := by
    have h2 : HasDerivAt (fun s => χ s ^ 2)
        ((2 : ℕ) * χ (aCoord H (u z)) ^ (2 - 1) * deriv χ (aCoord H (u z))) (aCoord H (u z)) :=
      (hχ (aCoord H (u z))).hasDerivAt.pow 2
    rw [h2.deriv]; push_cast; ring
  simp only [energyDensity, ds, dt, liouville]
  rw [hφ]
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  simp only [← omegaL_apply, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  have hanti : ∀ v : V n, omegaL v (w z) = -omegaL (w z) v := by
    intro v; rw [omegaL_apply, omegaL_apply, omega0_antisymm]
  rw [h0]
  simp only [hwdef] at hanti ⊢
  rw [hanti]
  ring

/-- On the circle, the boundary form of `χ(a) • w` is `χ(a)²` times that of `w`. -/
theorem bu_bdry_form {n : ℕ} (a : ℂ → ℝ) (w : ℂ → V n) (χ : ℝ → ℝ) (hχ : Differentiable ℝ χ)
    (z v : ℂ) (ha : DifferentiableAt ℝ a z) (hw : DifferentiableAt ℝ w z) :
    omegaL (χ (a z) • w z) (fderiv ℝ (fun z => χ (a z) • w z) z v) =
      χ (a z) ^ 2 * omegaL (w z) (fderiv ℝ w z v) := by
  have hca : HasFDerivAt (fun y => χ (a y)) (deriv χ (a z) • fderiv ℝ a z) z :=
    (hχ (a z)).hasDerivAt.comp_hasFDerivAt z ha.hasFDerivAt
  have hW : HasFDerivAt (fun z => χ (a z) • w z) _ z := hca.smul hw.hasFDerivAt
  rw [hW.fderiv]
  have h0 : omegaL (w z) (w z) = 0 := by
    rw [omegaL_apply]; have := omega0_antisymm (w z) (w z); linarith
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, map_add, map_smul, h0]
  ring

/-- Along the loops of a `C^∞`-converging family, the action integrand is eventually nonnegative. -/
theorem bu_eventually_nonneg {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (l : ℕ → ℝ → V n) (Q : ReebOrbit H) (hT : 0 < Q.T) (c : ℝ)
    (hconv : TendstoCInfty l (fun t => Q.x (Q.T * t + c))) :
    ∀ᶠ k in atTop, ∀ t, 0 ≤ liouville (l k t) (deriv (l k) t) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have hcpt := isCompact_energySurface H hH
  obtain ⟨A, hA⟩ := hcpt.exists_bound_of_continuousOn (f := fun x : V n => x) continuousOn_id
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn hK.continuousOn
  set Λ := ‖(omegaL : V n →L[ℝ] V n →L[ℝ] ℝ)‖ with hΛ
  have hΛn : 0 ≤ Λ := norm_nonneg (omegaL (n := n))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (Q.mem 0))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (Q.mem 0))
  have hder : ∀ t, deriv (fun t => Q.x (Q.T * t + c)) t = Q.T • reeb H (Q.x (Q.T * t + c)) := by
    intro t
    have hin : HasDerivAt (fun t : ℝ => Q.T * t + c) Q.T t := by
      simpa using ((hasDerivAt_id t).const_mul Q.T).add_const c
    exact ((Q.hasDerivAt (Q.T * t + c)).scomp t hin).deriv
  -- `L` is the constant `‖T • reeb‖` bound
  set L := Q.T * B with hL
  have hL0 : 0 ≤ L := mul_nonneg hT.le hB0
  -- choose the tolerance
  obtain ⟨ε, hε, hεs⟩ : ∃ ε > 0, Λ * ε * (L + ε) + Λ * A * ε < 2 * Q.T := by
    have hc : Continuous (fun ε : ℝ => Λ * ε * (L + ε) + Λ * A * ε) := by fun_prop
    have h0 : (fun ε : ℝ => Λ * ε * (L + ε) + Λ * A * ε) 0 < 2 * Q.T := by simpa using hT
    have hev := hc.continuousAt.eventually (gt_mem_nhds h0)
    obtain ⟨ε, hε1, hε2⟩ := (hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))) |>.exists
    exact ⟨ε, hε2, hε1⟩
  have h0 := Metric.tendstoUniformly_iff.1 (hconv 0) ε hε
  have h1 := Metric.tendstoUniformly_iff.1 (hconv 1) ε hε
  filter_upwards [h0, h1] with k hk0 hk1 t
  have ht0 := hk0 t
  have ht1 := hk1 t
  simp only [iteratedDeriv_zero, iteratedDeriv_one, hder] at ht0 ht1
  rw [dist_comm, dist_eq_norm] at ht0 ht1
  set x := Q.x (Q.T * t + c) with hx
  have hxS : x ∈ energySurface H := Q.mem _
  have hR := (reeb_spec H hH x hxS).2.1
  have hR2 : omegaL x (Q.T • reeb H x) = 2 * Q.T := by
    have h := hR
    rw [liouville, ← omegaL_apply] at h
    rw [map_smul, smul_eq_mul]
    have : omegaL x (reeb H x) = 2 := by linarith
    rw [this]; ring
  set a := l k t with ha
  set b := deriv (l k) t with hb
  set y := Q.T • reeb H x with hy
  have hby : ‖y‖ ≤ L := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos hT, hL]
    exact mul_le_mul_of_nonneg_left (hB _ hxS) hT.le
  have hbb : ‖b‖ ≤ L + ε := by
    have : b = y + (b - y) := by abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add hby ht1.le)
  have hsplit : omegaL a b = omegaL x y + (omegaL (a - x) b + omegaL x (b - y)) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    ring
  have he1 : |omegaL (a - x) b| ≤ Λ * ε * (L + ε) := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht0.le hΛn) hbb (norm_nonneg _)
      (mul_nonneg hΛn hε.le)
  have he2 : |omegaL x (b - y)| ≤ Λ * A * ε := by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA _ hxS) hΛn) ht1.le (norm_nonneg _)
      (mul_nonneg hΛn hA0)
  have hfin : 0 ≤ omegaL a b := by
    rw [hsplit, hR2]
    have := neg_abs_le (omegaL (a - x) b)
    have := neg_abs_le (omegaL x (b - y))
    linarith
  rw [liouville, ← omegaL_apply]
  linarith

/-- The Hofer energy of a nonconstant finite-energy plane equals its `dλ`-energy. -/
theorem energy_univ_eq_dlambdaEnergy_of_plane_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    energy H Set.univ u = dlambdaEnergy H Set.univ u := by
  obtain ⟨hnnφ, hnnd, hdle, -⟩ := energyDensity_nonneg H hH J hJ Set.univ isOpen_univ u hu
  refine le_antisymm ?_ hdle
  obtain ⟨hpos, -, -, hseq⟩ := plane_asymptotics H hH J hJ u hu hnc
  have htop : dlambdaEnergy H Set.univ u ≠ ⊤ := by
    intro h; rw [h] at hpos; simp at hpos
  set T := (dlambdaEnergy H Set.univ u).toReal with hTdef
  have hTe : dlambdaEnergy H Set.univ u = ENNReal.ofReal T := (ENNReal.ofReal_toReal htop).symm
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  have hw : ContDiff ℝ ∞ w :=
    contDiffOn_univ.1 (hprojs.comp hu.1 (fun z _ => hu.2.1 z (Set.mem_univ _)))
  have ha : ContDiff ℝ ∞ a :=
    contDiffOn_univ.1 (haCs.comp hu.1 (fun z _ => hu.2.1 z (Set.mem_univ _)))
  -- radii along which the action integrand is nonnegative
  obtain ⟨φ₀, hφ₀, Q, hQT, c, hconv⟩ := hseq (fun k => (k : ℝ)) tendsto_natCast_atTop_atTop
  have hQpos : 0 < Q.T := Q.T_pos
  have hevpos := bu_eventually_nonneg H hH _ Q hQpos c hconv
  have hφt : Tendsto (fun k => ((φ₀ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ₀.tendsto_atTop
  refine iSup₂_le fun φ hφ => ?_
  -- it suffices to bound all `(1 + ε)`-multiples
  have main : ∀ ε : ℝ, 0 < ε → ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H φ u z) ≤
      ENNReal.ofReal ((1 + ε) * T) := by
    intro ε hε
    set χ : ℝ → ℝ := fun s => Real.sqrt (φ s + ε) with hχdef
    have hφε : ∀ s, 0 < φ s + ε := fun s => by linarith [(hφ.2.2 s).1]
    have hχ : ContDiff ℝ ∞ χ :=
      (hφ.1.add contDiff_const).sqrt fun s => (hφε s).ne'
    have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
    have hχ2 : ∀ s, χ s ^ 2 = φ s + ε := fun s => Real.sq_sqrt (hφε s).le
    set W : ℂ → V n := fun z => χ (a z) • w z with hWdef
    have hW : ContDiff ℝ ∞ W := (hχ.comp ha).smul hw
    have had : ∀ z, DifferentiableAt ℝ a z := fun z => (ha.differentiable (by simp)) z
    have hwd : ∀ z, DifferentiableAt ℝ w z := fun z => (hw.differentiable (by simp)) z
    have hfun : (fun s => χ s ^ 2) = fun s => φ s + ε := funext hχ2
    have hden : ∀ z, omega0 (fderiv ℝ W z 1) (fderiv ℝ W z Complex.I) =
        energyDensity H (fun s => φ s + ε) u z := fun z => by
      rw [← hfun]
      exact bu_density_eq H u χ hχd z (had z) (hwd z)
    -- comparison with the density of `φ + ε`
    have hcmp : ∀ z, energyDensity H φ u z ≤ energyDensity H (fun s => φ s + ε) u z := by
      intro z
      have hd : deriv (fun s => φ s + ε) (a z) = deriv φ (a z) := by simp
      have hnn := hnnd z (Set.mem_univ _)
      simp only [dlambdaDensity] at hnn
      simp only [energyDensity]
      rw [show deriv (fun s => φ s + ε) (aCoord H (u z)) = deriv φ (aCoord H (u z)) from hd]
      nlinarith [mul_nonneg hε.le hnn]
    -- the disc bound
    have hball : ∀ᶠ k in atTop, ∫⁻ z in ball 0 ((φ₀ k : ℕ) : ℝ),
        ENNReal.ofReal (energyDensity H φ u z) ≤ ENNReal.ofReal ((1 + ε) * T) := by
      filter_upwards [hevpos, hφt.eventually (eventually_gt_atTop (0 : ℝ))] with k hk hR0
      set R : ℝ := ((φ₀ k : ℕ) : ℝ) with hRdef
      have hposθ : ∀ θ, 0 ≤ omegaL (w (circleMap 0 R θ))
          (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) := by
        intro θ
        have h := hk (θ / (2 * π))
        rw [bu_liouville_loop H u hw R (θ / (2 * π))] at h
        have e : 2 * π * (θ / (2 * π)) = θ := by field_simp
        rw [e] at h
        exact nonneg_of_mul_nonneg_right h Real.pi_pos
      have hbdry : buBdry W R ≤ (1 + ε) * buBdry w R := by
        unfold buBdry
        rw [show (1 + ε) * ((1 / 2) * ∫ θ in (0 : ℝ)..2 * π, omegaL (w (circleMap 0 R θ))
            (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I))) =
            (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, (1 + ε) * omegaL (w (circleMap 0 R θ))
            (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) by
          rw [intervalIntegral.integral_const_mul]; ring]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine intervalIntegral.integral_mono_on (by positivity)
          ((bu_continuous_bdry W hW R).intervalIntegrable _ _)
          (((bu_continuous_bdry w hw R).const_mul _).intervalIntegrable _ _) fun θ _ => ?_
        have hform := bu_bdry_form a w χ hχd (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)
          (had _) (hwd _)
        rw [show W (circleMap 0 R θ) = χ (a (circleMap 0 R θ)) • w (circleMap 0 R θ) from rfl,
          show fderiv ℝ W (circleMap 0 R θ) = fderiv ℝ (fun z => χ (a z) • w z) (circleMap 0 R θ)
            from rfl, hform, hχ2]
        refine mul_le_mul_of_nonneg_right ?_ (hposθ θ)
        linarith [(hφ.2.2 (a (circleMap 0 R θ))).2]
      -- `buBdry w R` is the action of the circle
      have hact : buBdry w R ≤ T := by
        rw [← bu_loopAction_eq H u hw R, loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hu R hR0]
        exact ENNReal.toReal_mono htop (lintegral_mono_set (Set.subset_univ _))
      have hint : IntegrableOn (fun z => energyDensity H (fun s => φ s + ε) u z) (ball 0 R) := by
        have hc : Continuous (fun z => energyDensity H (fun s => φ s + ε) u z) := by
          simp_rw [← hden]
          exact bu_continuous_dens W hW
        exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
          ball_subset_closedBall
      have hφεadm : ∀ z, 0 ≤ energyDensity H (fun s => φ s + ε) u z := fun z =>
        (hnnφ φ hφ z (Set.mem_univ _)).trans (hcmp z)
      calc ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H φ u z)
          ≤ ∫⁻ z in ball 0 R, ENNReal.ofReal (energyDensity H (fun s => φ s + ε) u z) :=
            lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hcmp z)
        _ = ENNReal.ofReal (∫ z in ball 0 R, energyDensity H (fun s => φ s + ε) u z) :=
            (ofReal_integral_eq_lintegral_ofReal hint
              (Eventually.of_forall hφεadm)).symm
        _ ≤ ENNReal.ofReal ((1 + ε) * T) := by
            refine ENNReal.ofReal_le_ofReal ?_
            simp_rw [← hden]
            rw [bu_ball_eq W hW R hR0]
            exact hbdry.trans (mul_le_mul_of_nonneg_left hact (by linarith))
    -- exhaust by balls
    set μ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (energyDensity H φ u z))
      with hμdef
    have hμ : ∀ s : Set ℂ, MeasurableSet s →
        ∫⁻ z in s, ENNReal.ofReal (energyDensity H φ u z) = μ s := fun s hs =>
      (withDensity_apply _ hs).symm
    have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) (N : ℝ)) := fun i j hij =>
      ball_subset_ball (by exact_mod_cast hij)
    have hunion : ⋃ N : ℕ, ball (0 : ℂ) (N : ℝ) = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
    have hN : ∀ N : ℕ, (μ ∘ fun N : ℕ => ball (0 : ℂ) (N : ℝ)) N ≤ ENNReal.ofReal ((1 + ε) * T) := by
      intro N
      rw [Function.comp_apply, ← hμ _ measurableSet_ball]
      obtain ⟨k, hk1, hk2⟩ := (hball.and (hφt.eventually (eventually_ge_atTop (N : ℝ)))).exists
      exact (lintegral_mono_set (ball_subset_ball hk2)).trans hk1
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion, ← hμ _ MeasurableSet.univ] at h
    exact le_of_tendsto' h hN
  -- let `ε → 0`
  rw [hTe]
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * T)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal T)) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * T)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun ε hε => main ε hε)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    energy H Set.univ u = dlambdaEnergy H Set.univ u :=
  energy_univ_eq_dlambdaEnergy_of_plane_aux H hH J hJ u hu hnc
