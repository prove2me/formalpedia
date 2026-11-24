-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Fw_lsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:11:58.020749+00:00
-- url     : https://prove2.me/submissions/0867b62f-8d4a-41d5-b6d7-cac995cc8c81

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Fw_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_ck_lsum

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
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (w : List (Ix k r)) :
    ∀ (L : List (ℂ × (Mat k r → E))), (∀ p ∈ L, CkOn ((w.length : ℕ) : ℕ∞) (GV k r) p.2) →
    ∀ g ∈ GV k r, Fw Eop w (fun x => (L.map fun p => p.1 • p.2 x).sum) g = (L.map fun p => p.1 • Fw Eop w p.2 g).sum := by
  intro L
  induction L with
  | nil =>
    intro _ g hg
    simp only [List.map_nil, List.sum_nil]
    exact Fw_zero Eop hC hL hS w g hg
  | cons p L ih =>
    intro h g hg
    have hL' : ∀ q ∈ L, CkOn ((w.length : ℕ) : ℕ∞) (GV k r) q.2 := fun q hq => h q (by simp [hq])
    have hs : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) (fun x => p.1 • p.2 x) := by
      intro g₀ hg₀
      obtain ⟨U, f', hU, hg', hc, he⟩ := h p (by simp) g₀ hg₀
      exact ⟨U, fun x => p.1 • f' x, hU, hg', hc.const_smul p.1, fun g hg hgG => by simp only [he g hg hgG]⟩
    have hr := ck_lsum L hL'
    simp only [List.map_cons, List.sum_cons]
    rw [Fw_add Eop hC hL hA w (fun x => p.1 • p.2 x) _ hs hr g hg,
      Fw_smul Eop hC hL hS w p.1 p.2 (h p (by simp)) g hg, ih hL' g hg]
end Formalism.FourierDecayAlt.P.JFxE
