-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.support_eq_initial_support_of_order_eq_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:22:15.332809+00:00
-- url     : https://prove2.me/submissions/3ed04072-69bb-4b61-802b-db34487ebb73

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_terminal_eq_initial_of_order_eq_nil

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (data : TerminalGrowth F) (horder : data.order = []) :
    data.support = F.support := by
  rw [support]
  rw [data.terminal_eq_initial_of_order_eq_nil horder]
end BKAR.Forest.TerminalGrowth
