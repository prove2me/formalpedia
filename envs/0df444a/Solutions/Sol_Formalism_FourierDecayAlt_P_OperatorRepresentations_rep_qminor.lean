-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.rep_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:53:08.223379+00:00
-- url     : https://prove2.me/submissions/18601b0b-c247-49da-93b3-be2429ded0d4

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_intCast_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_Tm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_qminor


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
theorem _root_.solution (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Rep (qminor (EV k r i D E) a b u) (fun f => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by
  refine ⟨Qx2.good_qminor hD a b u, fun φ g hg => ?_⟩
  have h := (rep_sum Finset.univ _ _ fun (σ : Equiv.Perm (Fin t)) _ =>
    (rep_prod t _ _ fun l : Fin t => rep_Tm (E := E) hD (u - (l : ℂ)) (a (σ l)) (b l)).intCast_mul
      (Equiv.Perm.sign σ : ℤ)).2 φ g hg
  unfold qminor
  rw [h]
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, Function.comp]
end Formalism.FourierDecayAlt.P.OperatorRepresentations
