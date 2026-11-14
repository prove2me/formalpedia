-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:22:20.087119+00:00
-- url     : https://prove2.me/submissions/5cc640b1-4f2b-4cfd-960d-a2e81615a8d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_positive_independent_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_omitted_negative_tail_integrable_L1_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Gaussian source independence, centring and genuine omitted-tail L1 combine. -/
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
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
      ProbabilityTheory.IndepFun (R t) J P ∧
        Integrable (R t) P ∧ Integrable J P ∧
        (∫ ω, R t ω ∂P) = 0 := by
  intro n t ht
  have hInd :=
    avram_a21_original_gaussian_limit_omitted_tail_positive_independent_20261113
      X hX hFinite R hR n t ht
  have hCentered :=
    avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
      X hX hFinite R hR t
  have hTail :=
    avram_a21_original_omitted_negative_tail_integrable_L1_20261113
      X hX hFinite R hR n t
  exact ⟨hInd, hCentered.1, hTail, hCentered.2⟩
