-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_actual_BV_original_cap_C1_deriv_uniformContinuousOn_compact_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:27:35.597265+00:00
-- url     : https://prove2.me/submissions/1a96af34-cf3c-4552-af88-7e0011293169

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Source HJB C¹ derivatives have one compact-band modulus, uniformly
across arbitrary stopped grid samples in the genuine positive cap interior. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    UniformContinuousOn (deriv w) (Icc a b) := by
  have hOpen : IsOpen
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  have hCont : ContinuousOn (deriv w) (Icc a b) :=
    (hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)).mono hBand
  haveI : CompactSpace (Icc a b : Set ℝ) :=
    (isCompact_iff_compactSpace).mp isCompact_Icc
  rw [uniformContinuousOn_iff_restrict]
  exact CompactSpace.uniformContinuous_of_continuous
    ((continuousOn_iff_continuous_restrict).mp hCont)
