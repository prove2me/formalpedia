-- Prove2me | solution 1 for AvramDividend.Classical.avram_a56_original_gaussian_true_stationary_independent_increments_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:18:04.651008+00:00
-- url     : https://prove2.me/submissions/596a7f25-253f-493d-8a10-42c2ad999527

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a55_stationary_increment_witness_implies_true_identdistrib_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ s t, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s t, s ≤ t →
        IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P) := by
  obtain ⟨G, hAdapt, hZero, hEq, hCont, hIndep, hStationary⟩ :=
    avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
      X hX hFinite R hR
  have hMeas (t : ℝ≥0) : Measurable (G t) :=
    (hAdapt t).mono (𝓕.le t) le_rfl
  have hIdent :=
    avram_a55_stationary_increment_witness_implies_true_identdistrib_20261114
      G hMeas hZero hStationary
  refine ⟨G, hAdapt, hZero, hEq, hCont, ?_, hIdent⟩
  intro s t hst
  convert hIndep s (t - s) using 1
  congr 1
  funext ω
  rw [add_tsub_cancel_of_le hst]
