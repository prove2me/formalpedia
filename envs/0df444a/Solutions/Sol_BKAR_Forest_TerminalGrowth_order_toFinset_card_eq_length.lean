-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.order_toFinset_card_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:30.377144+00:00
-- url     : https://prove2.me/submissions/bacf5317-260e-48b4-acd0-8a8d4b137042

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_card_eq_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.order.toFinset.card = data.order.length :=
  data.growth.order_toFinset_card_eq_length
end BKAR.Forest.TerminalGrowth
