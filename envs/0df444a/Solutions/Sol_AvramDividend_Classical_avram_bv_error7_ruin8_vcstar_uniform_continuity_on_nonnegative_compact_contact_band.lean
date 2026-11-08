-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:49:26.545198+00:00
-- url     : https://prove2.me/submissions/aef016e4-35f7-492a-9d33-69c368b68acc

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

/-- The genuine BV barrier value admits a uniform continuity modulus up to
the nonnegative ruin endpoint, without any uniform derivative bound there. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hbv : X.BoundedVariation) (B : ℝ) :
    UniformContinuousOn (vcstar W) (Set.Icc 0 B) := by
  have hcont : ContinuousOn (vcstar W) (Set.Ici 0) :=
    (vcstar_unrestricted_verification_regularity X hX q hq W hW hc
      (Or.inr (Or.inl hbv))).1
  have hsub : Set.Icc (0 : ℝ) B ⊆ Set.Ici 0 := by
    intro y hy
    exact hy.1
  exact isCompact_Icc.uniformContinuousOn_of_continuous (hcont.mono hsub)
