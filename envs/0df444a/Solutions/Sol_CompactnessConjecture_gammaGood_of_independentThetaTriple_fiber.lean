-- Prove2me | solution 1 for CompactnessConjecture.gammaGood_of_independentThetaTriple_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/d3b34362-6dfe-4166-8cd8-3675ff568349

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_gammaGood_of_three_common_centers

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
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) (vertex : V)
    (hvertex : vertex ∈ commonCenterFinset G triple.val)
    (hcard : 3 ≤ (commonCenterFinset G triple.val).card) :
    GammaGood G vertex := by
  apply gammaGood_of_three_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hvertex
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hcard
end CompactnessConjecture
