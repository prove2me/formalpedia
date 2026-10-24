-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_zero_origin_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:52:42.279297+00:00
-- url     : https://prove2.me/submissions/3797e5cb-0e3a-4dba-92bb-9598e63f9e92

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioo_of_continuousOn_all_compact_subintervals
import Theorems.Thm_AvramDividend_Classical_generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Compact residual continuity upgrades an a.e. C2 generator equation to pointwise harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by
  have hcompact : ∀ l u : ℝ, 0 < l → l < u → u < a →
      ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
        (Icc l u) := by
    intro l u hl hlu hu
    exact generator_residual_continuousOn_compact_of_zero_origin_C2
      X q W hW hzero a l u hl hlu hu hC2
  have hcontinuous : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioo 0 a) :=
    continuousOn_Ioo_of_continuousOn_all_compact_subintervals
      _ a ha hcompact
  exact generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
    X q W a hcontinuous hae
