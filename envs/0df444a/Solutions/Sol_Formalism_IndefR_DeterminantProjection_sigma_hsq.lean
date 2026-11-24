-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.sigma_hsq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:15.692071+00:00
-- url     : https://prove2.me/submissions/9ea8a44a-ec58-4a7d-a14f-779dbdce7e51

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
    (u : n → A) : σ (hsq σ J u) = hsq σ J u := by
  have h1 : σ (hsq σ J u) = ∑ i, (J *ᵥ u) i * σ (u i) := by
    simp only [hsq, dotProduct, map_sum, map_mul, sigma_rowJ σ hσ J hJ]
  rw [h1]
  show _ = rowJ σ J u ⬝ᵥ u
  rw [rowJ, ← dotProduct_mulVec]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end Formalism.IndefR.DeterminantProjection
