-- Prove2me | solution 1 for CompactnessConjecture.orderedThetaTripleCount_mul_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/f0df3415-dde8-45bc-abf0-2601cc9e3560

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_thetaBaseExtensions_card_mul_degree_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    orderedThetaTripleCount host * d ≤ n ^ 3 := by
  classical
  calc
    orderedThetaTripleCount host * d =
        ∑ y : Fin n, ∑ z : Fin n,
          (thetaBaseExtensions host y z).card * d := by
      simp [orderedThetaTripleCount, Finset.sum_mul]
    _ ≤ ∑ _y : Fin n, ∑ _z : Fin n, n := by
      gcongr with y _ z _
      exact thetaBaseExtensions_card_mul_degree_le
        host hfree hbip d hdegree y z
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]
end CompactnessConjecture
