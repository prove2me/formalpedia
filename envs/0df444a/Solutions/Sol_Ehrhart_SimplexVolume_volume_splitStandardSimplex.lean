-- Prove2me | solution 1 for Ehrhart.SimplexVolume.volume_splitStandardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/3104613e-3b13-4ca9-94b0-ca466183d778

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SimplexVolume_splitStandardSimplex_eq_preimage

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution (n : ℕ) :
    (volume : Measure (ℝ × Space n)) (splitStandardSimplex n) =
      (volume : Measure (Space (n + 1)))
        (standardSimplex (n + 1)) := by
  rw [splitStandardSimplex_eq_preimage]
  exact
    ((MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm).measure_preimage_equiv
      (standardSimplex (n + 1))
end Ehrhart.SimplexVolume
