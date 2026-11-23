-- Prove2me | solution 1 for Collect.mem_collect_iff_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:59.176215+00:00
-- url     : https://prove2.me/submissions/dd420bef-2249-4ee7-8a29-cf509b3ecf86

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
import Theorems.Thm_Collect_collect_spec
import Theorems.Thm_Collect_collect_spec_reverse

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect
namespace Collect
theorem _root_.solution {O : OBdd n m} {j : Fin m} :
    j ∈ collect O ↔ Pointer.Reachable O.1.heap O.1.root (.node j) := ⟨collect_spec_reverse, collect_spec⟩
end Collect
