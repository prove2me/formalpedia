-- Prove2me | solution 1 for FD1D.iterate_refreshedLaw_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:36.415031+00:00
-- url     : https://prove2.me/submissions/d4d384af-15a4-4342-bdb4-3815b921de33

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
import Theorems.Thm_FD1D_refreshedLaw_lawInvariant
import Theorems.Thm_FD1D_FiniteKernel_iterate_lawInvariant


set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L m : ℕ} (K : FiniteKernel (InventoryState (DyadicNode L) m))
    (leafPerm : Equiv.Perm (DyadicNode L))
    (hK : K.Equivariant (inventoryStatePerm leafPerm)) (n : ℕ) :
    FiniteKernel.LawInvariant (K.iterate n (refreshedLaw L m))
      (inventoryStatePerm leafPerm) :=
  FiniteKernel.iterate_lawInvariant hK
    (refreshedLaw_lawInvariant leafPerm) n
end FD1D
