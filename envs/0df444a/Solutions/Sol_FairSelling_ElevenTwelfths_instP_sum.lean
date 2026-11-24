-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.instP_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:08.805645+00:00
-- url     : https://prove2.me/submissions/d7933255-ff61-484b-a1fb-e1440ac8e3a3

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_FeigeNorkin
import Definitions.Def_RequestProject_ElevenTwelfths
import Theorems.Thm_FairSelling_ElevenTwelfths_cast_sum_eq
import Theorems.Thm_FairSelling_FeigeNorkin_fnU_total


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ElevenTwelfths
open FeigeNorkin
namespace FairSelling.ElevenTwelfths
theorem _root_.solution (δ : ℝ) : (∑ g, instP δ g) = 108 * δ := by
  have : (∑ g, instP δ g) = δ * ∑ g, (fnU g : ℝ) := by
    rw [Finset.mul_sum]; rfl
  rw [this, cast_sum_eq Finset.univ fnU 108 fnU_total]
  ring
end FairSelling.ElevenTwelfths
