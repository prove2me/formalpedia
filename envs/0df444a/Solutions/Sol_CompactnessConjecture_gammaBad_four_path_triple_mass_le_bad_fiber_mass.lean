-- Prove2me | solution 1 for CompactnessConjecture.gammaBad_four_path_triple_mass_le_bad_fiber_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/22cb9e01-adcf-4a62-b178-6b0da662826c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_badFourPathTripleToBadIndependentTriple_injective
import Theorems.Thm_CompactnessConjecture_badFourPathTripleWitness_card
import Theorems.Thm_CompactnessConjecture_badIndependentTripleWitness_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    (∑ u ∈ gammaBadVertices G,
      commonSecondNeighborTripleMass G u) ≤
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  rw [← badFourPathTripleWitness_card,
    ← badIndependentTripleWitness_card]
  exact Fintype.card_le_of_injective
    (badFourPathTripleToBadIndependentTriple
      G hbip hfour hsix)
    (badFourPathTripleToBadIndependentTriple_injective
      G hbip hfour hsix)
end CompactnessConjecture
