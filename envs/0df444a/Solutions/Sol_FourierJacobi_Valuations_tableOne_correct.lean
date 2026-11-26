-- Prove2me | solution 1 for FourierJacobi.Valuations.tableOne_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:28.468677+00:00
-- url     : https://prove2.me/submissions/010039af-6359-4782-9b43-1fc647797836

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (k j h c : ℤ) (hc : 0 ≤ c) :
    tableOne k j h c = cartanIndices 1 k j h c := by
  unfold tableOne collisionRows cartanIndices entryMinimum minorMinimum
    determinantValuation baseMinimum
  simp only [one_ne_zero, ite_false]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega
end FourierJacobi.Valuations
