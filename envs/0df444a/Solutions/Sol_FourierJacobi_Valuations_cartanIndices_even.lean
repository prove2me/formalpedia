-- Prove2me | solution 1 for FourierJacobi.Valuations.cartanIndices_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:52.430798+00:00
-- url     : https://prove2.me/submissions/7f3671e8-2ecb-4056-a21b-385d611f8732

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (r k j h c : ℤ) : Even (cartanIndices r k j h c).1 := by
  change Even (-2 * (minorMinimum r k j h c - entryMinimum r k j h))
  refine ⟨entryMinimum r k j h - minorMinimum r k j h c, ?_⟩
  omega
end FourierJacobi.Valuations
