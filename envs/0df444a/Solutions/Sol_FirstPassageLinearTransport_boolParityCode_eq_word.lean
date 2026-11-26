-- Prove2me | solution 1 for FirstPassageLinearTransport.boolParityCode_eq_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:15.779888+00:00
-- url     : https://prove2.me/submissions/b963310c-0a93-42ad-b777-3719f880cd9b

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
theorem _root_.solution (M : ℕ) (n : Fin (2 ^ M)) :
    boolParityCode M n = boolParityWord M n := rfl
end FirstPassageLinearTransport
