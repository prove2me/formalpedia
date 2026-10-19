-- Prove2me | solution 1 for Ehrhart.BergmanGeodesicConvexity.hasDerivAt_logarithmicSlope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/3feee813-6871-42f8-bf9b-aa1ee41490f5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanGeodesicConvexity
open Set Module
open scoped BigOperators InnerProductSpace
namespace Ehrhart.BergmanGeodesicConvexity
theorem _root_.solution {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (k t : ℝ) :
    HasDerivAt
      (fun q : ℝ => exponentialMoment w order 1 q /
        exponentialPartition w order q / k)
      ((exponentialMoment w order 2 t *
          exponentialPartition w order t -
        exponentialMoment w order 1 t *
        exponentialMoment w order 1 t) /
        (exponentialPartition w order t) ^ 2 / k) t := by
  exact ((hasDerivAt_exponentialMoment w order 1 t).fun_div
    (hasDerivAt_exponentialPartition w order t)
    (exponentialPartition_pos w order hw hpositive t).ne').div_const k
end Ehrhart.BergmanGeodesicConvexity
