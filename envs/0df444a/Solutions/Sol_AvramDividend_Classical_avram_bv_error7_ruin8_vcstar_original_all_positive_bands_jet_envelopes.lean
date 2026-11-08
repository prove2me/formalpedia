-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_original_all_positive_bands_jet_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:53:05.833486+00:00
-- url     : https://prove2.me/submissions/3939f683-6c1e-4196-8556-8b46fe37469a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original BV barrier C1 jet envelopes for any sequence of compact
interior reserve bands. The ruin boundary remains a distinct source cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    ∃ L : ℕ → ℝ,
      (∀ n, 0 ≤ L n) ∧
      (∀ n, ∀ y ∈ Set.Icc (a n) (b n), ∀ z ∈ Set.Icc (a n) (b n),
        |vcstar W z - vcstar W y| ≤ L n * |z - y|) ∧
      (∀ n, ∀ y ∈ Set.Icc (a n) (b n), |deriv (vcstar W) y| ≤ L n) := by
  classical
  have hExists : ∀ n : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ Set.Icc (a n) (b n), |deriv (vcstar W) y| ≤ L := by
    intro n
    exact avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
      X hX q hq W hW hc hcpos hbv (a n) (b n) (ha n)
  choose L hL hDeriv using hExists
  refine ⟨L, hL, ?_, hDeriv⟩
  intro n y hy z hz
  have hzy : y + (z - y) ∈ Set.Icc (a n) (b n) := by
    convert hz using 1 <;> ring
  have hContact := avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv
    X hX q hq W hW hc hcpos hbv (a n) (b n) (L n)
    (ha n) (hL n) (hDeriv n) y (z - y) hy hzy
  have hyz : y + (z - y) = z := by ring
  simpa [hyz] using hContact.1
