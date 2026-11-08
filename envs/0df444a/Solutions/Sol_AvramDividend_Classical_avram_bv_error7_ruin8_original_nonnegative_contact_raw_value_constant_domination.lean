-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:59:19.597668+00:00
-- url     : https://prove2.me/submissions/00a42e85-af9b-4a72-93da-552e081a7f60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine barrier raw contact change has an integrable constant
envelope on nonnegative compact reserves, even at the zero boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (B : ℝ)
    (z c : ℕ → Ω → ℝ)
    (hBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧ z m ω + c m ω ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m ω, ‖Err m ω‖ ≤ 2 * M := by
  obtain ⟨M, hM, hVal⟩ :=
    avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
      X hX q hq W hW hc hBV B
  refine ⟨M, hM, ?_⟩
  intro m ω
  have hleft := hVal (z m ω + c m ω) (hBand m ω).2
  have hright := hVal (z m ω) (hBand m ω).1
  rw [hErrSource m ω]
  rw [Real.norm_eq_abs]
  calc
    |vcstar W (z m ω + c m ω) - vcstar W (z m ω)| =
        |vcstar W (z m ω + c m ω) + -(vcstar W (z m ω))| := by simp only [sub_eq_add_neg]
    _ ≤ |vcstar W (z m ω + c m ω)| + |-(vcstar W (z m ω))| :=
      abs_add_le _ _
    _ = |vcstar W (z m ω + c m ω)| + |vcstar W (z m ω)| := by rw [abs_neg]
    _ ≤ M + M := add_le_add hleft hright
    _ = 2 * M := by ring
