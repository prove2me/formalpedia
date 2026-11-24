-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.parts_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:29.551212+00:00
-- url     : https://prove2.me/submissions/e76f6690-0cb5-4b5b-a8ff-d52f11bb84b4

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : ∀ j k : Fin 3, j ≠ k → Disjoint (parts j) (parts k) := by decide
end FairSelling.LemmaFourCounterexample
