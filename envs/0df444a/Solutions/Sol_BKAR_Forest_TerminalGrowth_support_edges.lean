-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.support_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:58:28.026677+00:00
-- url     : https://prove2.me/submissions/a4ecdaaa-0864-4fc7-9000-5fd69115f01a

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.support.edges = data.terminal.edges :=
  rfl
end BKAR.Forest.TerminalGrowth
