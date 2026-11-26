-- Prove2me | solution 1 for FirstPassageLinearTransport.boolParityWord_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:19.225978+00:00
-- url     : https://prove2.me/submissions/ab36b5d1-feae-4ce6-9803-a6fad41d294f

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
theorem _root_.solution (r n : ℕ) :
    (fun i : Fin r => boolParityWord (r + 1) n i.succ) =
      boolParityWord r (shortcut n) := by
  funext i
  unfold boolParityWord
  congr 1
end FirstPassageLinearTransport
