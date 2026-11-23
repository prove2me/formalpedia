-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.rowJ_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:12.809638+00:00
-- url     : https://prove2.me/submissions/db42bda7-5872-446a-931a-9d98fdc45eeb

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
theorem _root_.solution {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (j : n) :
    f (rowJ σ J u j) = rowJ σ' (J.map f) (fun i => f (u i)) j := by
  simp only [rowJ, vecMul, dotProduct, map_sum, map_mul, hf, Matrix.map_apply]
end Formalism.IndefR.DeterminantProjection
