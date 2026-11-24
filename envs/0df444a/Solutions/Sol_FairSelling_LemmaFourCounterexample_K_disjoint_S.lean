-- Prove2me | solution 1 for FairSelling.LemmaFourCounterexample.K_disjoint_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:39.922206+00:00
-- url     : https://prove2.me/submissions/369cc078-2e39-4b05-a834-5f3d80c4d8e3

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_LemmaFourNecessity

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.LemmaFourCounterexample
namespace FairSelling.LemmaFourCounterexample
theorem _root_.solution : Disjoint K S := by decide
end FairSelling.LemmaFourCounterexample
