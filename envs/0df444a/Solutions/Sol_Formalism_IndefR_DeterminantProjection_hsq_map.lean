-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.hsq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:02.362958+00:00
-- url     : https://prove2.me/submissions/80a63c1b-a467-4705-af13-9add8573fca7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
import Theorems.Thm_Formalism_IndefR_DeterminantProjection_rowJ_map

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
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) :
    f (hsq σ J u) = hsq σ' (J.map f) (fun i => f (u i)) := by
  simp only [hsq, dotProduct, map_sum, map_mul, rowJ_map f σ σ' hf]
end Formalism.IndefR.DeterminantProjection
