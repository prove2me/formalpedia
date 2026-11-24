-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:19.039797+00:00
-- url     : https://prove2.me/submissions/5bb3302b-d2a1-47fc-95c6-599d3b9a01c6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_ck
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ck_lsum
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
theorem _root_.solution (hC : HC Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + d : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (ev Eop a f) := by
  obtain ⟨L, hL, h⟩ := ev_rep_ex Eop ha
  have e : ev Eop a f = fun x => ((L.map fun p => (p.1, Fw Eop p.2 f)).map fun q => q.1 • q.2 x).sum := by
    funext x
    rw [h]
    simp [List.map_map, Function.comp_def]
  rw [e]
  apply ck_lsum
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact Fw_ck Eop hC p.2 m f (ck_mono' (by have := hL p hp; omega) hf)
end Formalism.FourierDecayAlt.P.JFxE
