-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Fw_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:19.299921+00:00
-- url     : https://prove2.me/submissions/653a2d78-d9b3-46fb-94db-a6b8be5e63df

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
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) : ∀ (w : List (Ix k r)) (f f₂ : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ →
    ∀ g ∈ GV k r, Fw Eop w (fun x => f x + f₂ x) g = Fw Eop w f g + Fw Eop w f₂ g := by
  intro w
  induction w with
  | nil => intro f f₂ _ _ g _; rfl
  | cons x w ih =>
    intro f f₂ hf hf₂ g hg
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ck_mono' (by simp) hf
    have hf₂' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ := ck_mono' (by simp) hf₂
    have e : 1 + w.length = (x :: w).length := by simp only [List.length_cons]; omega
    have c1 : CkOn 1 (GV k r) (Fw Eop w f) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f := by rw [e]; exact hf
      simpa using Fw_ck Eop hC w 1 f h'
    have c2 : CkOn 1 (GV k r) (Fw Eop w f₂) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f₂ := by rw [e]; exact hf₂
      simpa using Fw_ck Eop hC w 1 f₂ h'
    show Eop x.1 x.2 (Fw Eop w (fun y => f y + f₂ y)) g =
      Eop x.1 x.2 (Fw Eop w f) g + Eop x.1 x.2 (Fw Eop w f₂) g
    rw [hL x.1 x.2 _ (fun y => Fw Eop w f y + Fw Eop w f₂ y) (ih f f₂ hf' hf₂') g hg]
    exact hA x.1 x.2 _ _ c1 c2 g hg
end Formalism.FourierDecayAlt.P.JFxE
