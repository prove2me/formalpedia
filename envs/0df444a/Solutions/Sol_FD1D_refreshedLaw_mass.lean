-- Prove2me | solution 1 for FD1D.refreshedLaw_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:35.300054+00:00
-- url     : https://prove2.me/submissions/baefaf43-5016-44a1-8ba0-a5ae4779f3c5

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
namespace FD1D
theorem _root_.solution (L m : ℕ)
    (x : InventoryState (DyadicNode L) m) :
    (refreshedLaw L m).mass x =
      ∑ ω : DyadicAssignment L m with assignmentState ω = x,
        (1 / Fintype.card (DyadicAssignment L m) : ℝ) :=
  rfl
end FD1D
