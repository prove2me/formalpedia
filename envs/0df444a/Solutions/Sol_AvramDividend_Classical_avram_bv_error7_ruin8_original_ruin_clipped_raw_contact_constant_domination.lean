-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_original_ruin_clipped_raw_contact_constant_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:29:38.565224+00:00
-- url     : https://prove2.me/submissions/546dd994-b395-4dc5-85db-a7833158c4e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Ruin-crossing last contacts still enjoy a constant integrable envelope:
the candidate is exactly zero below ruin and bounded on the clipped band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (B : ℝ)
    (z c : ℕ → Ω → ℝ)
    (hClipBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧
      max (z m ω + c m ω) 0 ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m ω, ‖Err m ω‖ ≤ 2 * M := by
  obtain ⟨M, hM, hVal⟩ :=
    avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
      X hX q hq W hW hc hBV B
  refine ⟨M, hM, ?_⟩
  intro m ω
  have hleft : |vcstar W (z m ω + c m ω)| ≤ M := by
    rcases lt_or_ge (z m ω + c m ω) 0 with hneg | hpos
    · rw [vcstar_eq_zero_of_neg W _ hneg]
      simpa using hM
    · have hclip : max (z m ω + c m ω) 0 = z m ω + c m ω :=
        max_eq_left hpos
      exact hVal _ (by simpa only [hclip] using (hClipBand m ω).2)
  have hright := hVal (z m ω) (hClipBand m ω).1
  rw [hErrSource m ω, Real.norm_eq_abs]
  calc
    |vcstar W (z m ω + c m ω) - vcstar W (z m ω)| =
        |vcstar W (z m ω + c m ω) + -(vcstar W (z m ω))| := by
          rw [sub_eq_add_neg]
    _ ≤ |vcstar W (z m ω + c m ω)| + |-(vcstar W (z m ω))| :=
      abs_add_le _ _
    _ = |vcstar W (z m ω + c m ω)| + |vcstar W (z m ω)| := by rw [abs_neg]
    _ ≤ M + M := add_le_add hleft hright
    _ = 2 * M := by ring
