-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_chX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:33:53.022424+00:00
-- url     : https://prove2.me/submissions/17f7053c-d7f0-4da7-813e-a0bb772d1d34

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_etaV
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


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
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (x : Fin (mdim k r i) → ℂ) :
    Rep (chX (EV k r i D E) u x (etaV k r z i D E))
      (fun f => chatL (EH k r) (posL k r i) u (fun _ => x) (ybv k r z i) f) := by
  have h := rep_sum Finset.univ _ _ fun (a : Fin (mdim k r i)) _ => rep_sum Finset.univ _ _
    fun (b : Fin (mdim k r i)) _ => (((rep_etaV (E := E) hD z a).mul (rep_qminor hD (skip1 a) (skip1 b) u)).smul
      ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * x b))
  refine Eq.mp (congrArg (Rep _) ?_) h
  funext f g
  simp only [chatL, mulF, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring
end Formalism.FourierDecayAlt.P.OperatorRepresentations
