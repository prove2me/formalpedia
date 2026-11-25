-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:47.032459+00:00
-- url     : https://prove2.me/submissions/6db08882-cb61-4247-91d4-6bffbb0f6f77

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ev_rep_ex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) :
    ∀ g ∈ GV k r, ev Eop a (fun _ => (0 : E)) g = 0 := by
  obtain ⟨L, _, hrep⟩ := ev_rep_ex Eop ha
  intro g hg
  rw [hrep]
  apply List.sum_eq_zero
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨p, _, rfl⟩ := hy
  rw [Fw_zero Eop hC hL hS p.2 g hg, smul_zero]
end Formalism.FourierDecayAlt.P.JFxE
