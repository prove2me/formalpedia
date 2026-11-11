-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1a2_uniform_small_exp_remainder_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:01:39.322703+00:00
-- url     : https://prove2.me/submissions/fd2cee69-de5f-4d65-91ad-562d2eb50633

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_compensated_exponential_quadratic_of_small_argument

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Levy small-negative compensator is uniformly O(theta squared). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ K : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫ z in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) / θ ≤ K := by
  let S : Set ℝ := Ioo (-1 : ℝ) 0
  have hSqFinite :=
    finite_small_negative_jump_square_moment X.ν X.ν_integrable
  have hSqInt : IntegrableOn (fun z : ℝ => z ^ 2) S X.ν := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (by fun_prop : AEStronglyMeasurable (fun z : ℝ => z ^ 2)
        (X.ν.restrict S))
      (Filter.Eventually.of_forall (fun z : ℝ => sq_nonneg z))).1
    exact ne_of_lt (by simpa only [S] using hSqFinite)
  let K : ℝ := ∫ z in S, z ^ 2 ∂X.ν
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact integral_nonneg (fun z => sq_nonneg z)
  refine ⟨K, ?_⟩
  intro θ hθ hθOne
  have hθsq : θ ^ 2 ≤ 1 := by nlinarith
  have hDom : ∀ᵐ z ∂X.ν.restrict S,
      ‖Real.exp (θ * z) - 1 - θ * z‖ ≤ θ ^ 2 * z ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hneg : z < 0 := hz.2
    have hleft : -1 < z := hz.1
    have hsmall : ‖θ * z‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθ,
        abs_of_neg hneg]
      nlinarith
    exact compensated_exponential_quadratic_of_small_argument
      θ z hsmall
  have hRInt : IntegrableOn
      (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) S X.ν := by
    apply hSqInt.mono' (by fun_prop)
    filter_upwards [hDom] with z hz
    exact hz.trans (by nlinarith [sq_nonneg z] : θ ^ 2 * z ^ 2 ≤ z ^ 2)
  have hRle : (∫ z in S, Real.exp (θ * z) - 1 - θ * z ∂X.ν) ≤
      θ ^ 2 * K := by
    have hIntBound : IntegrableOn (fun z : ℝ => θ ^ 2 * z ^ 2) S X.ν :=
      hSqInt.const_mul (θ ^ 2)
    calc
      (∫ z in S, Real.exp (θ * z) - 1 - θ * z ∂X.ν) ≤
          (∫ z in S, θ ^ 2 * z ^ 2 ∂X.ν) := by
        apply integral_mono_ae hRInt hIntBound
        filter_upwards [hDom] with z hz
        exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hz)
      _ = θ ^ 2 * K := by rw [integral_const_mul]
  have hDiv : (∫ z in S, Real.exp (θ * z) - 1 - θ * z ∂X.ν) / θ ≤
      (θ ^ 2 * K) / θ :=
    div_le_div_of_nonneg_right hRle hθ.le
  have hFinal : (θ ^ 2 * K) / θ ≤ K := by
    have hcancel : (θ ^ 2 * K) / θ = θ * K := by
      field_simp [ne_of_gt hθ]
    rw [hcancel]
    exact mul_le_of_le_one_left hKnonneg hθOne
  simpa only [S, K] using hDiv.trans hFinal
