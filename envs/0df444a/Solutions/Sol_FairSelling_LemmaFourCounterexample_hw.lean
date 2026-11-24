-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.hw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:57.930732+00:00
-- url     : https://prove2.me/submissions/2d363977-fc63-405a-a27b-7ce6168892dd

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : ∀ g, 0 ≤ w g := fun _ => Nat.cast_nonneg _
end FairSelling.LemmaFourCounterexample
