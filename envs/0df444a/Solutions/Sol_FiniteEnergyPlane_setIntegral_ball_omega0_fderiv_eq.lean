-- Prove2me | solution 1 for FiniteEnergyPlane.setIntegral_ball_omega0_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T18:29:50.511249+00:00
-- url     : https://prove2.me/submissions/b3f087a0-94b4-49b0-89b3-5b56699b9454

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap



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

theorem setIntegral_ball_omega0_fderiv_eq_aux {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (R : ℝ)
    (hR : 0 < R) :
    ∫ z in ball 0 R, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, omega0 (w (circleMap 0 R θ))
        (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) := by
  have h := bu_ball_eq w hw R hR
  simpa only [buBdry, omegaL_apply] using h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (w : ℂ → V n) (hw : ContDiff ℝ ∞ w) (R : ℝ)
    (hR : 0 < R) :
    ∫ z in ball 0 R, omega0 (fderiv ℝ w z 1) (fderiv ℝ w z Complex.I) =
      (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, omega0 (w (circleMap 0 R θ))
        (fderiv ℝ w (circleMap 0 R θ) (circleMap 0 R θ * Complex.I)) :=
  setIntegral_ball_omega0_fderiv_eq_aux w hw R hR
