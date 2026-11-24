-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.wn_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:57.113324+00:00
-- url     : https://prove2.me/submissions/98eba6bb-34f4-4701-b33e-f541b2f95f9b

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : ∑ g, wn g = 150 := by decide
end FairSelling.LemmaFourCounterexample
