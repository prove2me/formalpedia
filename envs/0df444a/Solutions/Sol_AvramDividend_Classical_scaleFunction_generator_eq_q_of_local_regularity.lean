-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_local_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:25:50.460782+00:00
-- url     : https://prove2.me/submissions/e6adf8e5-96ed-400e-a503-dc5d91f9ecc6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_twoSidedExitIdentity_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hreg :
      (X.BoundedVariation ∧ ContDiffOn ℝ 1 W (Ioo 0 a)) ∨
      (¬ X.BoundedVariation ∧ ContDiffOn ℝ 2 W (Ioo 0 a))) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  have h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a) := by
    rcases hreg with hBV | hC2
    · exact Or.inr (Or.inl hBV.1)
    · exact Or.inr (Or.inr hC2.2)
  have hexit : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y =
        ENNReal.ofReal (W y / W b) := by
    intro b y hb hy0 hyb
    exact two_sided_exit_before_ruin_identity_corrected
      X hX q hq W hW b y hb hy0 hyb
  exact scaleFunction_generator_eq_q_of_twoSidedExitIdentity_corrected
    X hX q hq W hW a ha h_smooth hint hexit
