-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_succ_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:15.221427+00:00
-- url     : https://prove2.me/submissions/76b1eea4-777a-4dd2-9b9e-e5519f081422

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (H n : ℕ) :
    oddCount n (H + 1) =
      (parityBit n 0 : ℕ) + oddCount (shortcut n) H := by
  calc
    oddCount n (H + 1) =
        (parityBit n 0 : ℕ) +
          ∑ i ∈ Finset.range H, (parityBit n (i + 1) : ℕ) := by
      unfold oddCount
      rw [Finset.sum_range_succ']
      ac_rfl
    _ = (parityBit n 0 : ℕ) +
          ∑ i ∈ Finset.range H, (parityBit (shortcut n) i : ℕ) := by
      congr 1
    _ = (parityBit n 0 : ℕ) + oddCount (shortcut n) H := by
      rfl
end FirstPassageLinearTransport
