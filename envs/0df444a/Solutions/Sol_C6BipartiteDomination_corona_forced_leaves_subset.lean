-- Prove2me | solution 1 for C6BipartiteDomination.corona_forced_leaves_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:30.471035+00:00
-- url     : https://prove2.me/submissions/f016c405-14de-4a7b-8644-26c7a6d9f8be

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_leaf_forced

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D) :
    coronaForcedLeaves D ⊆ D := by
  classical
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  exact corona_leaf_forced hD
    ((Finset.mem_sdiff.mp (Finset.mem_product.mp hp |>.1)).2) p.2
end C6BipartiteDomination
