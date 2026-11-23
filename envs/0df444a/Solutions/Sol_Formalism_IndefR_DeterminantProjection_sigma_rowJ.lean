-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.sigma_rowJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:18.817992+00:00
-- url     : https://prove2.me/submissions/7aca60b5-6aac-4438-9f8e-28e1743c56ab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection

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
    (u : n → A) (i : n) : σ (rowJ σ J u i) = (J *ᵥ u) i := by
  simp only [rowJ, vecMul, mulVec, dotProduct, map_sum, map_mul, hσ, hJ]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end Formalism.IndefR.DeterminantProjection
