-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.hp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:00.918673+00:00
-- url     : https://prove2.me/submissions/36ee3bb1-016b-46db-a740-21bdfaf3ace2

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : ∀ g, 0 ≤ p g := fun _ => le_refl 0
end FairSelling.LemmaFourCounterexample
