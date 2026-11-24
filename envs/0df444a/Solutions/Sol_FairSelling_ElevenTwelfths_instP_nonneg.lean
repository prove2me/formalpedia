-- Prove2me | solution 1 for FairSelling.ElevenTwelfths.instP_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:54.148269+00:00
-- url     : https://prove2.me/submissions/7dfe0cfb-c2b5-46ad-a06a-1d81b88991b8

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
theorem _root_.solution {δ : ℝ} (hδ : 0 ≤ δ) : ∀ g, 0 ≤ instP δ g := by
  intro g; exact mul_nonneg hδ (by positivity)
end FairSelling.ElevenTwelfths
