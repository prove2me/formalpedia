-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.free_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:36.76925+00:00
-- url     : https://prove2.me/submissions/1d88be4e-22b8-4ce0-9438-39af150a9278

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
theorem _root_.solution {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (u y : Ix S) (h : u a ≠ y a) :
    G u y = 0 := by
  have e := congrFun (congrFun (hG (u a) (u a)).eq u) y
  rw [Formalism.FourierDecayAlt.P.Wd1.eU_mul_apply, Formalism.FourierDecayAlt.P.Wd1.mul_eU_apply] at e
  simp only [if_true, Function.update_eq_self] at e
  rw [e, if_neg (Ne.symm h)]
end Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
