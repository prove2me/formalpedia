-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.proj_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:27.387022+00:00
-- url     : https://prove2.me/submissions/dcc05b69-7c6f-49bf-8edb-6b102e14df58

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
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (ainv : A) :
    (proj σ J u ainv).map f = proj σ' (J.map f) (fun i => f (u i)) (f ainv) := by
  ext i j
  simp only [proj, Matrix.map_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.smul_apply,
    smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, map_mul, rowJ_map f σ σ' hf]
end Formalism.IndefR.DeterminantProjection
