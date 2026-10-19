-- Prove2me | solution 1 for CompactnessConjecture.booleanCut_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/c48c5fa9-abef-41cb-82ea-f0219b314f35

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : booleanCut G color ≤ G := by
  intro u v huv
  exact huv.1
end CompactnessConjecture
