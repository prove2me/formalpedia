-- Prove2me | solution 1 for CompactnessConjecture.thetaBaseExtensions_card_mul_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/4a36414b-6680-4108-8cea-6b5977019290

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_commonNeighborIndependent_card_mul_degree_le
import Theorems.Thm_CompactnessConjecture_thetaBaseExtensions_commonNeighborIndependent

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (y z : Fin n) :
    (thetaBaseExtensions host y z).card * d ≤ n := by
  simpa using
    (commonNeighborIndependent_card_mul_degree_le
      host (thetaBaseExtensions host y z)
      (thetaBaseExtensions_commonNeighborIndependent
        host hfree hbip y z)
      d hdegree)
end CompactnessConjecture
