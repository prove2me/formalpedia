-- Prove2me | solution 1 for CompactnessConjecture.badFourPathTripleWitness_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/b8a9fda0-f71d-40f1-85bf-1e3973e65d54

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_mem_gammaBadVertices
import Theorems.Thm_CompactnessConjecture_commonSecondNeighborFinset_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V) :
    Fintype.card (BadFourPathTripleWitness G) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_coe,
    Finset.card_powersetCard, commonSecondNeighborFinset_card]
  change
    (∑ u : {u : V // ¬ GammaGood G u},
      commonSecondNeighborTripleMass G u) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u
  symm
  apply Finset.sum_subtype
    (gammaBadVertices G)
    (fun u => (mem_gammaBadVertices G u))
end CompactnessConjecture
