-- Prove2me | solution 1 for FD1D.SupplyConfiguration.ofCountState_location
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:43:18.335809+00:00
-- url     : https://prove2.me/submissions/952ce40f-432c-4e65-b382-592e346d07a9

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_Realization

set_option autoImplicit true
open FD1D
noncomputable section
open Set
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (x : InventoryState (DyadicNode L) m) (j : Fin m) :
    (ofCountState x).location j =
      dyadicCellLeft ((ofCountState x).leaf j) :=
  rfl
end FD1D.SupplyConfiguration
