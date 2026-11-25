-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.Phi_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:38.040695+00:00
-- url     : https://prove2.me/submissions/ec4a5d32-4b8f-453d-bd08-0d598694479b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA

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
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (X : Submodule R U) :
    LinearMap.range (Phi T hRT X) = Submodule.span T (tm K K₁ '' (X : Set U)) := by
  unfold Phi
  erw [LinearMap.range_liftBaseChange]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
end Formalism.L2.Pj.QAt.TieLDA
