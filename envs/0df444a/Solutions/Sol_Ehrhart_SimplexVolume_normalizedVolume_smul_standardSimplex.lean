-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_smul_standardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/f125c35f-5ef9-4501-a5bf-530520c66d48

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) :
    normalizedVolume (r • standardSimplex n) =
      r ^ n * normalizedVolume (standardSimplex n) := by
  unfold normalizedVolume
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg
    (volume : Measure (Space n)) hr,
    Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr n)]
end Ehrhart.SimplexVolume
