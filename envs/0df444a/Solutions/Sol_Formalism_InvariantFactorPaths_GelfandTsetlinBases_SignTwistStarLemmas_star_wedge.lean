-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.star_wedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:55:27.601793+00:00
-- url     : https://prove2.me/submissions/64e7b157-15bf-459e-b8b8-78ee10a8331e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_sg_compl
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sgR_mul_self


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution (A : Form R n) (Y : Fin n → R) : star (wedgeF A Y) = contrF (star A) Y := by
  funext J
  simp only [star, wedgeF, contrF]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∉ J := by simpa using hm
  have e1 : epsN (insert m J) = (n + 1 + m.val) + epsN J := by
    unfold epsN; rw [Finset.sum_insert hm']
  have e2 : ((-1 : R)) ^ (n + 1 + m.val) = ((sg Jᶜ m : ℤ) : R) * ((sg J m : ℤ) : R) := by
    rw [← Int.cast_mul, sg_compl]; push_cast; rfl
  have e3 := sgR_mul_self (R := R) J m
  rw [Finset.compl_insert, e1, pow_add, e2]
  linear_combination (-(((-1 : R)) ^ epsN J * ((sg Jᶜ m : ℤ) : R) * A (Jᶜ.erase m) * Y m)) * e3
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
