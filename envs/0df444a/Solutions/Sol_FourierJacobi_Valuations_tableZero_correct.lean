-- Prove2me | solution 1 for FourierJacobi.Valuations.tableZero_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:02.86911+00:00
-- url     : https://prove2.me/submissions/6f8d7a81-50c6-4f5c-8baf-35689eefe557

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (k j h c : ℤ) :
    tableZero k j h = cartanIndices 0 k j h c := by
  unfold tableZero cartanIndices entryMinimum minorMinimum baseMinimum
  simp only [ite_true]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega
end FourierJacobi.Valuations
