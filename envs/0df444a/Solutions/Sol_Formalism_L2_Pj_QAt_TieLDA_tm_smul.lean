-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.tm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:51.733789+00:00
-- url     : https://prove2.me/submissions/d52ae951-2e89-4ca8-a39e-ae154f961781

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_smulR_def

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
theorem _root_.solution (r : R) (u : U) : tm K K₁ (r • u) = algebraMap R T r • tm K K₁ u := by
  have h := (tmR (K₁ := K₁) (K := K) (U := U) (R := R)).map_smul r u
  change tm K K₁ (r • u) = r • tm K K₁ u at h
  rw [h, smulR_def, smulT_def, hRT, smulK_eq]
end Formalism.L2.Pj.QAt.TieLDA
