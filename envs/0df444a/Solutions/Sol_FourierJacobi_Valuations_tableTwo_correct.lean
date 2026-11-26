-- Prove2me | solution 1 for FourierJacobi.Valuations.tableTwo_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:03.817492+00:00
-- url     : https://prove2.me/submissions/ec255ff5-e593-4eb1-9397-1315a3c18aa3

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Valuations
theorem _root_.solution (k j h c : ℤ) (hc : 0 ≤ c) :
    tableTwo k j h c = cartanIndices 2 k j h c := by
  unfold tableTwo collisionRows cartanIndices entryMinimum minorMinimum
    determinantValuation baseMinimum
  simp only [show (2 : ℤ) ≠ 0 by decide, ite_false]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega
end FourierJacobi.Valuations
