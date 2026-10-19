-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_centeredSimplex_eq_scale_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/b487640e-f939-4cc8-b60f-32ab401163cc

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
theorem _root_.solution (n : ℕ) :
    normalizedVolume (centeredSimplex n) =
      ((n : ℝ) + 1) ^ n *
        normalizedVolume (standardSimplex n) := by
  have hscale : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hset : centeredSimplex n =
      (fun x : Space n => x + (-1 : Space n)) ''
        (((n : ℝ) + 1) • standardSimplex n) := by
    unfold centeredSimplex
    rw [← Set.image_smul, Set.image_image]
    congr 1
  unfold normalizedVolume
  rw [hset]
  simp only [Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_smul_of_nonneg (volume : Measure (Space n)) hscale,
    Module.finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hscale n)]
end Ehrhart.SimplexVolume
