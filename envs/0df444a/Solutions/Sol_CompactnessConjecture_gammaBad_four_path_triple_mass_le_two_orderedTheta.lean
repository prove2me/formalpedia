-- Prove2me | solution 1 for CompactnessConjecture.gammaBad_four_path_triple_mass_le_two_orderedTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/32343c40-7e58-435b-9cb6-93678e72d794

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_gamma_bad_triple_fiber_mass_le_two_orderedTheta
import Theorems.Thm_CompactnessConjecture_gammaBad_four_path_triple_mass_le_bad_fiber_mass

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
    (∑ u ∈ gammaBadVertices host,
      commonSecondNeighborTripleMass host u) ≤
      2 * orderedThetaTripleCount host := by
  exact (gammaBad_four_path_triple_mass_le_bad_fiber_mass
    host hbip hfour hsix).trans
      (gamma_bad_triple_fiber_mass_le_two_orderedTheta
        host hbip hfour hsix)
end CompactnessConjecture
