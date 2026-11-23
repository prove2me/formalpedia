-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.adj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:55.318703+00:00
-- url     : https://prove2.me/submissions/8821e1db-f6e3-414c-85b7-da67e536d5d9

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) (I : Ideal (TruncK K' n))
    (hI : ∀ i j, adjugate Φ i j ∈ I) (i0 : Fin a) :
    (TT) ^ (∑ j ∈ Finset.univ.erase i0, k j) ∈ I := by
  classical
  have h1 : adjugate (P * Φ * Q) = adjugate Q * (adjugate Φ * adjugate P) := by
    rw [adjugate_mul_distrib, adjugate_mul_distrib]
  have h2 : ∀ i j, adjugate (P * Φ * Q) i j ∈ I := by
    intro i j
    rw [h1, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => I.mul_mem_left _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => I.mul_mem_right _ (hI l m)
  have h3 := h2 i0 i0
  rw [hD, adjugate_diagonal, diagonal_apply_eq, Finset.prod_pow_eq_pow_sum] at h3
  exact h3
end Formalism.CyclotomicNorms.residueMatrixData
