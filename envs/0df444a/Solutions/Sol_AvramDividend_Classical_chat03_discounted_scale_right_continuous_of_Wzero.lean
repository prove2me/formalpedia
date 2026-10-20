-- Prove2me | solution 1 for AvramDividend.Classical.chat03_discounted_scale_right_continuous_of_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:13:32.747991+00:00
-- url     : https://prove2.me/submissions/3bf5b123-a92d-45b6-9ea3-f997ec9bf144

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_everywhere
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Pathwise right-continuity of the discounted q-scale process, including
crossings of reserve zero, conditional only on W(0)=0 and continuous
discount. This is the regularity step for optional-stopping limits.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (discount : ℝ≥0 → ℝ) (hdiscount : Continuous discount)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => discount s * W (x + X.X s ω))
      (Set.Ici t) t := by
  have hWAt : ContinuousAt W (x + X.X t ω) :=
    chat03_scale_zero_extension_continuous_everywhere X q W hW hzero _
  have hAdd : ContinuousAt (fun y : ℝ => x + y) (X.X t ω) :=
    continuousAt_const.add continuousAt_id
  have hScale : Tendsto
      (fun s : ℝ≥0 => W (x + X.X s ω))
      (𝓝[Set.Ici t] t)
      (𝓝 (W (x + X.X t ω))) :=
    (hWAt.comp hAdd).tendsto.comp (X.rightCont ω t).tendsto
  have hDiscount : Tendsto discount (𝓝[Set.Ici t] t)
      (𝓝 (discount t)) :=
    (hdiscount.continuousAt.continuousWithinAt).tendsto
  exact hDiscount.mul hScale
