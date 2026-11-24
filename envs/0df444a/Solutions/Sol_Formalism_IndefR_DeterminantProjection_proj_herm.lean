-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.proj_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:12.803508+00:00
-- url     : https://prove2.me/submissions/ed631af0-d38f-4fcd-a191-8f78bb02679d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_sigma_rowJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.IndefR.DeterminantProjection
theorem _root_.solution (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (hainv : σ ainv = ainv) :
    J * proj σ J u ainv = ((proj σ J u ainv).map σ)ᵀ * J := by
  ext i j
  have lhs : (J * proj σ J u ainv) i j = (J *ᵥ u) i * (ainv * rowJ σ J u j) := by
    simp only [proj, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.smul_apply, smul_eq_mul,
      Finset.univ_unique, Finset.sum_singleton, mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hrow : rowJ σ J u j = ∑ k, σ (u k) * J k j := rfl
  have rhs : (((proj σ J u ainv).map σ)ᵀ * J) i j = σ (ainv * rowJ σ J u i) * rowJ σ J u j := by
    rw [hrow, Finset.mul_sum]
    simp only [proj, Matrix.mul_apply, transpose_apply, map_apply, replicateCol_apply, replicateRow_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, map_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [lhs, rhs, map_mul, hainv, sigma_rowJ σ hσ J hJ]
  ring
end Formalism.IndefR.DeterminantProjection
