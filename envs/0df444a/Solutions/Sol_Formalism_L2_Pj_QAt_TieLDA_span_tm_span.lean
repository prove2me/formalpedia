-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.span_tm_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:05:10.154793+00:00
-- url     : https://prove2.me/submissions/6947c140-ec8d-4848-970c-bf3b5dfdb7eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_tm_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
attribute [local instance] modT
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]
variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))
include hRT
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (G : Set U) :
    Submodule.span T (tm K K₁ '' (Submodule.span R G : Set U)) = Submodule.span T (tm K K₁ '' G) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      show (1 : K₁) ⊗ₜ[K] (0 : U) ∈ _
      rw [tmul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
      rw [tmul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [tm_smul T hRT]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
end Formalism.L2.Pj.QAt.TieLDA
