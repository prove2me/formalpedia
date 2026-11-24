-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.hpart1_I_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:30.845936+00:00
-- url     : https://prove2.me/submissions/4be6834e-04fd-4efe-a91c-8b23871d46b9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_two_I_inv

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
theorem _root_.solution (Z : Mat k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  simp only [neg_smul, neg_neg, sub_neg_eq_add]
  rw [← smul_add, smul_smul, show (1 / 2 : ℂ) * Complex.I = Complex.I / 2 by ring]
end Formalism.FourierDecayAlt.P.JFxE
