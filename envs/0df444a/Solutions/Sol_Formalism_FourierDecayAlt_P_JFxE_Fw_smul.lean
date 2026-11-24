-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Fw_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:18.108802+00:00
-- url     : https://prove2.me/submissions/856e13ef-9d0a-4a4c-b56f-51c87005c9d7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_ck
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862

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
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) : ∀ (w : List (Ix k r)) (c : ℂ) (f : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r, Fw Eop w (fun x => c • f x) g = c • Fw Eop w f g := by
  intro w
  induction w with
  | nil => intro c f _ g _; rfl
  | cons x w ih =>
    intro c f hf g hg
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ck_mono' (by simp) hf
    have e : 1 + w.length = (x :: w).length := by simp only [List.length_cons]; omega
    have c1 : CkOn 1 (GV k r) (Fw Eop w f) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f := by rw [e]; exact hf
      simpa using Fw_ck Eop hC w 1 f h'
    show Eop x.1 x.2 (Fw Eop w (fun y => c • f y)) g = c • Eop x.1 x.2 (Fw Eop w f) g
    rw [hL x.1 x.2 _ (fun y => c • Fw Eop w f y) (ih c f hf') g hg]
    exact hS x.1 x.2 c _ c1 g hg
end Formalism.FourierDecayAlt.P.JFxE
