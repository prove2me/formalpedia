-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.free_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:20:54.683114+00:00
-- url     : https://prove2.me/submissions/273c9748-2fc5-42e1-9793-9e1171294d4a

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
theorem _root_.solution {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (u y : Ix S) (i : Fin 2) :
    G (Function.update u a i) (Function.update y a i) = G (Function.update u a 0) (Function.update y a 0) := by
  have e := congrFun (congrFun (hG i 0).eq (Function.update u a i)) (Function.update y a 0)
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply] at e
  simp only [Function.update_self, if_true, Function.update_idem] at e
  exact e.symm
end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
