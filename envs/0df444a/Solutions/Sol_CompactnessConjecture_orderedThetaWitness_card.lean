-- Prove2me | solution 1 for CompactnessConjecture.orderedThetaWitness_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/23324b16-ffef-43e4-87ba-fef7fb38a265

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n)) :
    Fintype.card (OrderedThetaWitness host) =
      orderedThetaTripleCount host := by
  classical
  simp [OrderedThetaWitness, orderedThetaTripleCount,
    Fintype.card_sigma, Fintype.card_coe]
end CompactnessConjecture
