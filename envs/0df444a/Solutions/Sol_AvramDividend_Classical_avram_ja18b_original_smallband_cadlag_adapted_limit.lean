-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18b_original_smallband_cadlag_adapted_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:01:10.386243+00:00
-- url     : https://prove2.me/submissions/ea9ebdd8-365d-4275-9ba2-0e9d5db6aa41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18d_original_smallband_limit_rightcont_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja18e_original_smallband_locally_uniform_cadlag_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical path constructor and independent dominated adaptedness
closure together give the exact original right-filtration path theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont t) P (Jsmall t) ω = Jsmall t ω) := by
  obtain ⟨Jsmall, hLimit, hRight, hZero⟩ :=
    avram_ja18e_original_smallband_locally_uniform_cadlag_limit X hX hFinite
  exact ⟨Jsmall, hLimit, hRight, hZero,
    avram_ja18d_original_smallband_limit_rightcont_adapted
      X hFinite Jsmall hLimit⟩
