-- Prove2me | solution 1 for C6BipartiteDomination.corona_degree_at_most_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:54.144996+00:00
-- url     : https://prove2.me/submissions/d831c425-83aa-49ef-ab94-a4819b47ecba

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_core_degree
import Theorems.Thm_C6BipartiteDomination_corona_leaf_degree

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution :
    ∀ v, degreeTo coronaGraph Finset.univ v ≤ 6 := by
  intro v
  cases v with
  | inl i => rw [corona_core_degree i]
  | inr p => rw [corona_leaf_degree p.1 p.2]; norm_num
end C6BipartiteDomination
