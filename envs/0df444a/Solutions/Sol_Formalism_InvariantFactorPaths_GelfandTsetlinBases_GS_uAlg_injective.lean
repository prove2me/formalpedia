-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.uAlg_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:55.640249+00:00
-- url     : https://prove2.me/submissions/1e92a078-0fa2-4c9e-93d6-e31b5348bbd8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_uAlg_algebraMap

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
theorem _root_.solution (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det)
    (hinj : Function.Injective (aeval (R := k) (fun p : Fin n × Fin n => g₀ p.1 p.2))) :
    Function.Injective (uAlg k g₀ h) := by
  have : Function.Injective (uAlg k g₀ h : UR k n →+* B) := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (uDet k n))]
    intro x y
    simp only [RingHom.coe_coe]
    rw [uAlg_algebraMap, uAlg_algebraMap, hinj.eq_iff]
    refine (IsLocalization.injective (UR k n) (M := Submonoid.powers (uDet k n)) ?_).eq_iff
    exact powers_le_nonZeroDivisors_of_noZeroDivisors (Matrix.det_mvPolynomialX_ne_zero _ k)
  exact this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
