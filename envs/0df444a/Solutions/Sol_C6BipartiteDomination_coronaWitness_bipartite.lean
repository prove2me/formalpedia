-- Prove2me | solution 1 for C6BipartiteDomination.coronaWitness_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:30.93411+00:00
-- url     : https://prove2.me/submissions/d1ff8125-5e5d-42d6-8316-7a0da4367c56

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_C6BipartiteDomination_Corona

set_option autoImplicit true
open C6BipartiteDomination
set_option maxHeartbeats 1000000
namespace C6BipartiteDomination
theorem _root_.solution : IsBipartiteOn coronaGraph coronaWitness := by
  refine ⟨fun v => if v = Sum.inl 0 then true else false, ?_⟩
  intro u v hu hv hadj
  fin_cases u <;> fin_cases v <;>
    simp_all [coronaWitness, coronaGraph, coronaAdj]
end C6BipartiteDomination
