-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.uAlg_gen_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:51.127225+00:00
-- url     : https://prove2.me/submissions/0c96f256-0cec-4b3e-9a59-446bffc42835

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_uAlg_injective
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_algebraMap_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable (k : Type*) [Field k] (n : ℕ)
variable {k n}
variable {B : Type*} [CommRing B] [Algebra k B]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution : Function.Injective (uAlg k (genMat k n) genMat_isUnit) := by
  apply uAlg_injective
  have : (aeval (R := k) (fun p : Fin n × Fin n => genMat k n p.1 p.2) : _ →+* GenField k n) =
      algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [algebraMap_gen]
    · intro p
      simp [genMat]
  intro x y hxy
  have h1 := DFunLike.congr_fun this x
  have h2 := DFunLike.congr_fun this y
  simp only [RingHom.coe_coe] at h1 h2
  rw [h1, h2] at hxy
  exact IsFractionRing.injective _ (GenField k n) hxy
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
