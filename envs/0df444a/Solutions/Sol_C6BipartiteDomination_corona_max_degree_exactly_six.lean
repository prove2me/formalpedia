-- Prove2me | solution 1 for C6BipartiteDomination.corona_max_degree_exactly_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:39.52033+00:00
-- url     : https://prove2.me/submissions/65b4db6a-7c09-4ecd-84bc-a2e1d3fbb6e0

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
import Theorems.Thm_C6BipartiteDomination_corona_degree_at_most_six
import Theorems.Thm_C6BipartiteDomination_corona_degree_six

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
namespace C6BipartiteDomination
theorem _root_.solution :
    (∀ v, degreeTo coronaGraph Finset.univ v ≤ 6) ∧
      (∃ v, degreeTo coronaGraph Finset.univ v = 6) :=
  ⟨corona_degree_at_most_six, corona_degree_six⟩
end C6BipartiteDomination
