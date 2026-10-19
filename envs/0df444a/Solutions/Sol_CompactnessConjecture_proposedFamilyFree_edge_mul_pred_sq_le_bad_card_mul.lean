-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/f004704c-321a-4689-b0d7-84b0f56ad8ac

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_four_cycle
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_six_cycle
import Theorems.Thm_CompactnessConjecture_girthEight_degree_mul_pred_sq_le_card
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_edge_card_le_gammaBad_degree_sum

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
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n := by
  classical
  calc
    host.edgeFinset.card * (d - 1) ^ 2 ≤
        (∑ u ∈ gammaBadVertices host, host.degree u) *
          (d - 1) ^ 2 :=
      Nat.mul_le_mul_right ((d - 1) ^ 2)
        (proposedFamilyFree_edge_card_le_gammaBad_degree_sum
          host hfree hbip)
    _ = ∑ u ∈ gammaBadVertices host,
        host.degree u * (d - 1) ^ 2 := by
      simp [Finset.sum_mul]
    _ ≤ ∑ _u ∈ gammaBadVertices host, n := by
      gcongr with u hu
      simpa using girthEight_degree_mul_pred_sq_le_card
        host hbip (proposedFamilyFree_four_cycle hfree)
        (proposedFamilyFree_six_cycle hfree) d hdegree u
    _ = (gammaBadVertices host).card * n := by simp
end CompactnessConjecture
