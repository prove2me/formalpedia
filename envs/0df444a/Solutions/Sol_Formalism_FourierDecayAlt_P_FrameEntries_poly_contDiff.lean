-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.poly_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:12:33.565818+00:00
-- url     : https://prove2.me/submissions/3c83cf7a-866f-4838-81d7-2b47ce34412e

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_sum


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution
    (p : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ) :
    ContDiff ℝ ∞ fun g : Mx k r => MvPolynomial.eval
      (Sum.elim (fun x => g x.1 x.2) (fun x => (Hpk k r * gᴴ * Hpk k r) x.1 x.2)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Mx k r => a)
  | add p q hp hq =>
    simpa only [map_add] using hp.add hq
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    cases n with
    | inl x =>
      simp only [Sum.elim_inl]
      exact (entL k r x.1 x.2).contDiff
    | inr x =>
      simp only [Sum.elim_inr, Matrix.mul_apply, Matrix.conjTranspose_apply]
      refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
      refine ContDiff.sum fun d _ => ContDiff.mul contDiff_const ?_
      exact Complex.conjCLE.contDiff.comp (entL k r c d).contDiff
end Formalism.FourierDecayAlt.P.FrameEntries
