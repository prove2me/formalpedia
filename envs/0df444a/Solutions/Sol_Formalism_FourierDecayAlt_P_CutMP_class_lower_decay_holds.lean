-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:40.986635+00:00
-- url     : https://prove2.me/submissions/e44701d8-5385-4c13-a99a-d0a4e6e85cc8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_opsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_prodBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution : JDCCLower := by
  intro k r Wp Wq _ _ _ _ _ _ Θ d A hd hG F hF hFA
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hΦck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word F) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) T.word_lie x (by simpa [wL] using hx))
    simpa using hF
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  refine ⟨?_, fun m => ?_⟩
  · rw [hop]
    clear hop
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) :=
        Pr.ck hO hcov ⟨(hG T (by simp)).1, hΦck T (by simp), fun g _ hg => by simp at hg⟩
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hΦck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · rw [hop]
    refine InCC_opsum Θ (fun T => ap T.coef (B.Rw T.word F)) ?_
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ : B.InCC (A - d + d) m (B.Rw T.word F) := by
      rw [sub_add_cancel]; exact InCC_Rw T.word_lie (hFA _)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hc (fun g _ hg => by simp at hg)⟩
end Formalism.FourierDecayAlt.P.CutMP
