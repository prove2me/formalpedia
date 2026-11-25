-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.isTorsionFree_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:35.150705+00:00
-- url     : https://prove2.me/submissions/7d0cc5a0-63d2-41cd-b4a9-2807104ef885

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
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
include K
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (X : Submodule R U) : Module.IsTorsionFree R X := by
  constructor
  intro r hr x y hxy
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  apply Subtype.ext
  have h1 : r • (x : U) = r • (y : U) := congrArg Subtype.val hxy
  rw [← algebraMap_smul K r (x : U), ← algebraMap_smul K r (y : U)] at h1
  exact smul_right_injective U hK h1
end Formalism.L2.Pj.QAt.TieLDA
