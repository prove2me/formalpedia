-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:49:42.190237+00:00
-- url     : https://prove2.me/submissions/fa6a13fe-6493-4cb4-a062-f991b8aedbc6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A uniform absolute value envelope for the genuine barrier candidate
includes zero, and therefore does not rely on bounded derivative at ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hbv : X.BoundedVariation) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc 0 B, |vcstar W z| ≤ M := by
  have hcont : ContinuousOn (vcstar W) (Set.Ici 0) :=
    (vcstar_unrestricted_verification_regularity X hX q hq W hW hc
      (Or.inr (Or.inl hbv))).1
  have hsub : Set.Icc (0 : ℝ) B ⊆ Set.Ici 0 := by
    intro y hy
    exact hy.1
  have hcontAbs : ContinuousOn (fun y => |vcstar W y|) (Set.Icc 0 B) :=
    (hcont.mono hsub).abs
  have hcompact : IsCompact ((fun y => |vcstar W y|) '' Set.Icc 0 B) :=
    isCompact_Icc.image_of_continuousOn hcontAbs
  rcases hcompact.bddAbove with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hM (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
