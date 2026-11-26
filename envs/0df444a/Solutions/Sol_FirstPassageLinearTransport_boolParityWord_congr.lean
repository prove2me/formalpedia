-- Prove2me | solution 1 for FirstPassageLinearTransport.boolParityWord_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:05.243396+00:00
-- url     : https://prove2.me/submissions/a755b699-08cb-47ec-a20b-8c99fb9fe5a5

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_parityPrefix_congr


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {M n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ M]) :
    boolParityWord M n = boolParityWord M n' := by
  exact congrArg (fun f : Fin M → Fin 2 => fun i => finTwoEquiv (f i))
    (parityPrefix_congr h)
end FirstPassageLinearTransport
