-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:31:18.42117+00:00
-- url     : https://prove2.me/submissions/97f3cc38-02d9-419a-b671-13b4b00f8f84

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_ck
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_lsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_lsum_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) {d e : ℕ} {a b : AA k r E}
    (ha : Rep d a) (hb : Rep e b) (f : Mat k r → E) (hf : CkOn ((d + e : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (a * b) f g = ev Eop a (ev Eop b f) g := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  have hev : ev Eop b f = fun x => ((Lb.map fun q => (q.1, Fw Eop q.2 f)).map fun q => q.1 • q.2 x).sum := by
    funext x
    simp only [ev, hb', lsum_apply, List.nil_append, Pi.smul_apply, Phi, List.map_map, Function.comp_def]
  intro g hg
  show a (b (Phi Eop f)) [] g = a (Phi Eop (ev Eop b f)) [] g
  rw [ha', ha', lsum_apply, lsum_apply]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [List.nil_append, Pi.smul_apply]
  congr 1
  have hck : ∀ q ∈ Lb.map (fun q => (q.1, Fw Eop q.2 f)), CkOn ((p.2.length : ℕ) : ℕ∞) (GV k r) q.2 := by
    intro q' hq'
    simp only [List.mem_map] at hq'
    obtain ⟨q, hq, rfl⟩ := hq'
    exact Fw_ck Eop hC q.2 p.2.length f (ck_mono' (by have := hLa p hp; have := hLb q hq; omega) hf)
  show b (Phi Eop f) p.2 g = Fw Eop p.2 (ev Eop b f) g
  rw [hev, Fw_lsum Eop hC hL hA hS p.2 _ hck g hg, hb', lsum_apply]
  simp only [List.map_map, Function.comp_def, Pi.smul_apply, Phi, Fw_append]
end Formalism.FourierDecayAlt.P.JFxE
