-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_time_cross_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:15:36.95869+00:00
-- url     : https://prove2.me/submissions/b1101a5d-5253-4a72-97b4-167d65861b0b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical Gaussian limit is orthogonal to the omitted compensated negative mark tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      (∫ ω, R t ω *
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ∂P) = 0 := by
  intro n t ht
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
  have h :=
    avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
      X hX hFinite R hR n t ht
  change IndepFun (R t) J P ∧
    Integrable (R t) P ∧ Integrable J P ∧
    (∫ ω, R t ω ∂P) = 0 at h
  have hInd : IndepFun (R t) J P := h.1
  have hRint : Integrable (R t) P := h.2.1
  have hJint : Integrable J P := h.2.2.1
  have hRcenter : (∫ ω, R t ω ∂P) = 0 := h.2.2.2
  have hProd :=
    hInd.integral_fun_mul_eq_mul_integral hRint.1 hJint.1
  change (∫ ω, R t ω * J ω ∂P) =
    (∫ ω, R t ω ∂P) * (∫ ω, J ω ∂P) at hProd
  rw [hRcenter, zero_mul] at hProd
  exact hProd
