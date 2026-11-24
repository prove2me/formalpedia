-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.cast_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:48.084176+00:00
-- url     : https://prove2.me/submissions/eaf612b8-9395-46cc-99b3-b76151fa48d6

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin
namespace FairSelling.ElevenTwelfths
theorem _root_.solution (s : Finset (Fin 8)) (w : Fin 8 → ℕ) (m : ℕ) (h : ∑ g ∈ s, w g = m) :
    ∑ g ∈ s, (w g : ℝ) = m := by
  rw [← Nat.cast_sum, h]
end FairSelling.ElevenTwelfths
