-- Prove2me | solution 1 for FourierJacobi.Valuations.entry_minor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:19.800744+00:00
-- url     : https://prove2.me/submissions/b5120c98-823c-4860-9927-5a0d00ce3fee

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (r k j h c : ℤ) (hc : 0 ≤ c) :
    2 * entryMinimum r k j h ≤ minorMinimum r k j h c ∧
      minorMinimum r k j h c ≤ entryMinimum r k j h := by
  unfold entryMinimum minorMinimum baseMinimum determinantValuation
  split_ifs <;> omega
end FourierJacobi.Valuations
