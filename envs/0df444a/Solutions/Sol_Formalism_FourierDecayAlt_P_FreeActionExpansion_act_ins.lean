-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.act_ins
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:47.374932+00:00
-- url     : https://prove2.me/submissions/410169dc-46ba-4493-ba5b-6a691bb23605

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (a : S) (M : M2 A) (Ψ : Ix S → V) (z : Ix S) :
    act (ins a (lift0 M)) Ψ z = ∑ j, M (z a) j • Ψ (Function.update z a j) := by
  have h : ∀ z', (ins a (lift0 M) : SlopeTestRemainingChoices S A) z z' =
      ∑ j, if z' = Function.update z a j then M (z a) j else 0 := by
    intro z'
    unfold ins lift0
    simp only [Matrix.sum_apply, Matrix.map_apply]
    have hm : ∀ i j, (((eU a i j : SlopeTestRemainingChoices S A) * (io (M i j) : SlopeTestRemainingChoices S A) : SlopeTestRemainingChoices S A)) z z' =
        if z a = i ∧ z' = Function.update z a j then M i j else 0 := by
      intro i j
      simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Formalism.FourierDecayAlt.P.Wd1.eU_apply, ite_mul,
        one_mul, zero_mul]
    simp only [hm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (z a)]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  unfold act
  simp only [h, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
end Formalism.FourierDecayAlt.P.FreeActionExpansion
