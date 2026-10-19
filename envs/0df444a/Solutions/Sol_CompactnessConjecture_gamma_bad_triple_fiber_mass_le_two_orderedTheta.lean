-- Prove2me | solution 1 for CompactnessConjecture.gamma_bad_triple_fiber_mass_le_two_orderedTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/6ab7fc89-30bb-4d89-a908-0beba9dc116d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_finite_bad_fiber_mass_le_two
import Theorems.Thm_CompactnessConjecture_gammaGood_of_independentThetaTriple_fiber
import Theorems.Thm_CompactnessConjecture_independentThetaTriple_card_le_orderedThetaTripleCount

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    finiteBadFiberMass
        (fun triple : IndependentThetaTriple host =>
          commonCenterFinset host triple.val)
        (GammaGood host) ≤
      2 * orderedThetaTripleCount host := by
  exact (finite_bad_fiber_mass_le_two _ _ (fun triple vertex hvertex hcard =>
    gammaGood_of_independentThetaTriple_fiber
      host hbip hfour hsix triple vertex hvertex hcard)).trans
    (Nat.mul_le_mul_left 2
      (independentThetaTriple_card_le_orderedThetaTripleCount
        host hbip hfour hsix))
end CompactnessConjecture
