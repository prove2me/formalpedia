-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:39:48.45287+00:00
-- url     : https://prove2.me/submissions/f7515fe7-8493-45b7-8f46-fe9835b2f9f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_on_positive_bv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual BV barrier derivative is bounded on every band bounded away
from ruin; its behaviour at zero is deliberately left open. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) (a b : ℝ) (ha : 0 < a) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ Set.Icc a b, |deriv (vcstar W) z| ≤ L := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_lt_of_le ha hz.1
  have hcont : ContinuousOn (fun z => |deriv (vcstar W) z|) (Set.Icc a b) :=
    ((vcstar_deriv_continuous_on_positive_bv X hX q hq W hW hc hcpos hbv).mono hsub).abs
  have hcompact : IsCompact ((fun z => |deriv (vcstar W) z|) '' Set.Icc a b) :=
    isCompact_Icc.image_of_continuousOn hcont
  rcases hcompact.bddAbove with ⟨L, hL⟩
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hL (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
