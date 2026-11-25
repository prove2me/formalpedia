-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.Phi_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:47.465488+00:00
-- url     : https://prove2.me/submissions/9aade233-f8a1-43eb-b75d-10629f3949ae

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
theorem _root_.solution (X : Submodule R U) (t : T) (x : X) :
    Phi T hRT X (t ⊗ₜ x) = (t : K₁) • tm K K₁ (x : U) := by
  unfold Phi
  erw [LinearMap.liftBaseChange_tmul]
  rfl
end Formalism.L2.Pj.QAt.TieLDA
