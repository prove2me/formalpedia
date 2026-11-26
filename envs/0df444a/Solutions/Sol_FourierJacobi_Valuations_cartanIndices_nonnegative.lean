-- Prove2me | solution 1 for FourierJacobi.Valuations.cartanIndices_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:17.888955+00:00
-- url     : https://prove2.me/submissions/3612c8e7-5287-4914-af6b-a55e7cfc42b9

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Theorems.Thm_FourierJacobi_Valuations_entry_minor_bounds

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (r k j h c : ℤ) (hc : 0 ≤ c) :
    0 ≤ (cartanIndices r k j h c).1 ∧ 0 ≤ (cartanIndices r k j h c).2 := by
  have hb := entry_minor_bounds r k j h c hc
  unfold cartanIndices
  simp only
  omega
end FourierJacobi.Valuations
