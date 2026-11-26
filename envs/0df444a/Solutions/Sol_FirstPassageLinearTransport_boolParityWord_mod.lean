-- Prove2me | solution 1 for FirstPassageLinearTransport.boolParityWord_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:25:02.895703+00:00
-- url     : https://prove2.me/submissions/d3e55a2e-1b35-456a-a53e-1994c877f158

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_boolParityWord_congr

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (M n : ℕ) :
    boolParityWord M (n % (2 ^ M)) = boolParityWord M n := by
  apply boolParityWord_congr
  show n % 2 ^ M % 2 ^ M = n % 2 ^ M
  exact Nat.mod_mod _ _
end FirstPassageLinearTransport
