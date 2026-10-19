-- Prove2me | solution 1 for Ehrhart.Geometry.isCompact_standardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/397d8652-1033-4a65-a9aa-8215de2219c8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_Geometry_isClosed_standardSimplex

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Geometry
open Set MeasureTheory
open scoped BigOperators
namespace Ehrhart.Geometry
theorem _root_.solution (n : ℕ) :
    IsCompact (standardSimplex n) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (0 : Space n)) (b := 1))
    (isClosed_standardSimplex n)
  intro x hx
  constructor
  · exact hx.1
  · intro i
    change x i ≤ 1
    exact (Finset.single_le_sum (fun j _ => hx.1 j)
      (Finset.mem_univ i)).trans hx.2
end Ehrhart.Geometry
