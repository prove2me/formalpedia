-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_Tm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:41:36.737452+00:00
-- url     : https://prove2.me/submissions/23b73172-2c68-4e81-a04f-e958adabbc2b

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_algebraMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ite
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_EV
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_ite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_posL_inj
import Theorems.Thm_QnYLeibnizW_posL_inj


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
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Tm (EV k r i D E) u a b) (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  refine ⟨Qx2.good_top hD u a b, fun φ g hg => ?_⟩
  have h := (((rep_algebraMap (k := k) (r := r) (i := i) (D := D) (E := E) u).ite (a = b)).add (rep_EV hD a b)).2 φ g hg
  have e : (posL k r i a = posL k r i b) = (a = b) := propext (Qx2.posL_inj i).eq_iff
  unfold Tm
  rw [h]
  simp only [QuantumDeterminants.Top, e]
end Formalism.FourierDecayAlt.P.OperatorRepresentations
