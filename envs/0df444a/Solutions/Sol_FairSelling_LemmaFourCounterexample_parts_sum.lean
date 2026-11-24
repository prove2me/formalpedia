-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.parts_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:05.453642+00:00
-- url     : https://prove2.me/submissions/f8a0fe97-c093-4222-b4e6-c4f61bfa37db

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : ∀ j, ∑ g ∈ parts j, wn g = 50 := by decide
end FairSelling.LemmaFourCounterexample
