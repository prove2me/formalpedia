-- Prove2me | solution 1 for C6BipartiteDomination.coronaWitness_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:27.187066+00:00
-- url     : https://prove2.me/submissions/05283c1e-3e27-414b-b273-5bfa32fc386b

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_C6BipartiteDomination_Corona

set_option autoImplicit true
open C6BipartiteDomination
namespace C6BipartiteDomination
theorem _root_.solution : Dominates coronaGraph coronaWitness := by
  intro v hv
  fin_cases v <;>
    simp_all [coronaWitness, coronaGraph, coronaAdj]
end C6BipartiteDomination
