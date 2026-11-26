-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.cons_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:28.203156+00:00
-- url     : https://prove2.me/submissions/3a4e4e71-accc-42f9-bd7c-8e0b6322c83a

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).order = e :: tail.order :=
  rfl
end BKAR.Forest.TerminalGrowth
