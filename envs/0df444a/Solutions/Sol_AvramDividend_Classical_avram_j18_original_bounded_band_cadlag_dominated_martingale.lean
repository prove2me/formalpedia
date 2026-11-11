-- Prove2me | solution 1 for AvramDividend.Classical.avram_j18_original_bounded_band_cadlag_dominated_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:14:04.336078+00:00
-- url     : https://prove2.me/submissions/04cd8b46-54cf-48ff-ac0b-600a57bbe3a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_smallband_physical_path_envelopes
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_martingale_limit
import Theorems.Thm_AvramDividend_Classical_avram_anoise29_original_bounded_compensated_band_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Separate original physical jump-count path regularity and envelopes
from the exact dominated conditional martingale limiting argument. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ, ∃ B : Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, Jsmall 0 ω = 0) ∧
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖Jsmall t ω‖ ≤ B ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Jsmall, hLim, hRight, hZero, hSelf, hBounds⟩ :=
    avram_ja18_original_smallband_physical_path_envelopes X hX hFinite
  let J : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω
  have hCutoff := avram_anoise29_original_bounded_compensated_band_martingale
    X hFinite
  have hInt : ∀ k t, Integrable (J k t) P :=
    fun k t => (hCutoff k).1 t
  have hMart : ∀ (k : ℕ) (s t : ℝ≥0), s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (J k t) ω = J k s ω :=
    fun k s t hst => (hCutoff k).2 s t hst
  obtain ⟨hZInt, hZMart⟩ :=
    avram_ja18_original_dominated_martingale_limit
      J Jsmall hInt hMart hLim hSelf hBounds
  obtain ⟨B, hBi, hZdom, _⟩ := hBounds (n : ℝ≥0)
  exact ⟨Jsmall, B, hLim, hZInt, hZMart, hRight, hZero, hBi, hZdom⟩
