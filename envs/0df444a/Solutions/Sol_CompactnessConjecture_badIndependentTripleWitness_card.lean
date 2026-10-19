-- Prove2me | solution 1 for CompactnessConjecture.badIndependentTripleWitness_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/50987fc5-09e0-419e-8fd2-9fbb71d7d1ed

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V) :
    Fintype.card (BadIndependentTripleWitness G) =
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  classical
  rw [Fintype.card_sigma]
  unfold finiteBadFiberMass
  apply Finset.sum_congr
  · rfl
  · intro triple htriple
    rw [Fintype.card_subtype]
    congr 1
    ext center
    simp
end CompactnessConjecture
