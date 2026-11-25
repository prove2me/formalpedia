-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.freeOf_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:55.88669+00:00
-- url     : https://prove2.me/submissions/0668be0d-1d43-47fc-bf3f-161db7b3050f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_mul_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
theorem _root_.solution (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  refine Matrix.ext fun z z' => ?_
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply]
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h1 : z a = i <;> by_cases h2 : z' a = j
  · simp only [h1, h2, if_true]
    by_cases h3 : Function.update z a j = z'
    · have h4 : z = Function.update z' a i := by rw [← h3]; simp [← h1]
      rw [if_pos h3, if_pos h4]
    · have h4 : z ≠ Function.update z' a i := by
        intro h4; apply h3; rw [h4]; simp [← h2]
      rw [if_neg h3, if_neg h4]
  · have : Function.update z a j ≠ z' := by intro h3; apply h2; rw [← h3]; simp
    rw [if_pos h1, if_neg h2, if_neg this]
  · have : z ≠ Function.update z' a i := by intro h3; apply h1; rw [h3]; simp
    rw [if_neg h1, if_pos h2, if_neg this]
  · rw [if_neg h1, if_neg h2]
end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
