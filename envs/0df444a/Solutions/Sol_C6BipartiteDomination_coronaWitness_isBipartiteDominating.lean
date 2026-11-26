-- Prove2me | solution 1 for C6BipartiteDomination.coronaWitness_isBipartiteDominating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:37.980881+00:00
-- url     : https://prove2.me/submissions/6cb4fcc4-5d9d-45ab-9887-cc372aee1050

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_C6BipartiteDomination_Corona
import Theorems.Thm_C6BipartiteDomination_coronaWitness_dominates
import Theorems.Thm_C6BipartiteDomination_coronaWitness_bipartite

set_option autoImplicit true
open C6BipartiteDomination
namespace C6BipartiteDomination
theorem _root_.solution :
    IsBipartiteDominatingSet coronaGraph coronaWitness :=
  ⟨coronaWitness_dominates, coronaWitness_bipartite⟩
end C6BipartiteDomination
