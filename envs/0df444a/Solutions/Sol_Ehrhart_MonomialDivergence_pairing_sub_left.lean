-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.pairing_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/e3a85ebe-af02-46ff-880d-8a864832c478

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.MonomialDivergence
theorem _root_.solution {n : ℕ}
    (a b x : Space n) :
    SupportFunction.pairing (a - b) x =
      SupportFunction.pairing a x -
        SupportFunction.pairing b x := by
  simp [SupportFunction.pairing, sub_mul,
    Finset.sum_sub_distrib]
end Ehrhart.MonomialDivergence
