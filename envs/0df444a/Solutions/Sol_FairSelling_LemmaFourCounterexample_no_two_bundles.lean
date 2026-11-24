-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.no_two_bundles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:06:21.686406+00:00
-- url     : https://prove2.me/submissions/d9b247cc-9022-447a-a56a-309d669ee261

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : ∀ A B : Finset (Option (Fin 6)), Disjoint A B →
    (∑ x ∈ A, cwn x) ≤ 37 ∨ (∑ x ∈ B, cwn x) ≤ 37 := by
  decide +kernel
end FairSelling.LemmaFourCounterexample
