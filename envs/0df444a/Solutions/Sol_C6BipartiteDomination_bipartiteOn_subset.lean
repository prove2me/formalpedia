-- Prove2me | solution 1 for C6BipartiteDomination.bipartiteOn_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:54.623412+00:00
-- url     : https://prove2.me/submissions/e805ecb4-5392-43f9-bc17-322b892cc559

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D E : Finset V} (hE : E ⊆ D)
    (hD : IsBipartiteOn G D) : IsBipartiteOn G E := by
  rcases hD with ⟨c, hc⟩
  exact ⟨c, fun {u v} hu hv hAdj => hc (hE hu) (hE hv) hAdj⟩
end C6BipartiteDomination
