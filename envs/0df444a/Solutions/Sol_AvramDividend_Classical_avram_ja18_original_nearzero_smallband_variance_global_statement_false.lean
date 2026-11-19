-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_nearzero_smallband_variance_global_statement_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:26:12.650771+00:00
-- url     : https://prove2.me/submissions/d6733206-77c5-4004-a266-60d23fa1fe76

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A concrete original Standing model refutes the universal complementary-band identity. -/
theorem solution :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω]
        {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕)
        (_hX : X.Standing)
        (_hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤),
      ∀ (n : ℕ) (t : ℝ≥0),
        (∫ ω,
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
          (t : ℝ) *
            (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) := by
  intro hUniversal
  obtain ⟨P, 𝓕, X, hX, hFinite, hCounter⟩ :=
    avram_ja18_uniform_compound_Standing_counterexample_nearzero_variance_identity
  exact hCounter (hUniversal X hX hFinite)
