-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_twoSidedExitIdentity_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T10:20:25.462238+00:00
-- url     : https://prove2.me/submissions/e37c9dd2-95ab-4882-8cf0-d02b840bf066
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Convert the ratio-form corrected exit identity into the product-form
stopped identity using strict positivity of the scale function, then apply
the conditional local Dynkin result. The imported Dynkin theorem is Open. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hexit : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y =
        ENNReal.ofReal (W y / W b)) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  have hstop : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y *
        ENNReal.ofReal (W b) = ENNReal.ofReal (W y) := by
    intro b y hb hy0 hyb
    rw [hexit b y hb hy0 hyb]
    have hWb : 0 < W b :=
      scaleFunction_strict_pos_of_standing X hX q hq W hW b hb
    calc
      ENNReal.ofReal (W y / W b) * ENNReal.ofReal (W b) =
          ENNReal.ofReal ((W y / W b) * W b) := by
            exact (ENNReal.ofReal_mul' hWb.le).symm
      _ = ENNReal.ofReal (W y) := by
        congr 1
        exact div_mul_cancel₀ (W y) hWb.ne'
  exact scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
    X hX q hq W hW a ha h_smooth hint hstop
