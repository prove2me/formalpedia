-- Prove2me | solution 1 for FD1D.inventoryStatePerm_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:36.694982+00:00
-- url     : https://prove2.me/submissions/ef2c66f9-051f-49c9-a227-9bf0d2931b2f

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution {ι : Type*} [Fintype ι]
    {m : ℕ} (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryStatePerm e x).1 i = x.1 (e.symm i) :=
  rfl
end FD1D
