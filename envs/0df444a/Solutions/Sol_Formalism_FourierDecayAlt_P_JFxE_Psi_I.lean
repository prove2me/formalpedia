-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Psi_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:46.808343+00:00
-- url     : https://prove2.me/submissions/d7405aff-f67d-4c5c-99ef-c953d16adadd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart1_I_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_hpart2_I_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : Psi D g (Complex.I • Z) = Complex.I • Psi D g Z := by
  simp only [Psi, hpart1_I_smul, hpart2_I_smul, Matrix.mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel
end Formalism.FourierDecayAlt.P.JFxE
