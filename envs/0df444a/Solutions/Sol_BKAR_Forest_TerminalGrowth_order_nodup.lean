-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.order_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:09.828916+00:00
-- url     : https://prove2.me/submissions/f8ff1a0d-60fa-4a26-bc60-107bf5091576

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.order.Nodup :=
  data.growth.order_nodup
end BKAR.Forest.TerminalGrowth
