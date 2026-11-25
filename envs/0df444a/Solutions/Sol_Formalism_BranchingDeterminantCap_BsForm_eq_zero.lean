-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.BsForm.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:42.328366+00:00
-- url     : https://prove2.me/submissions/3b267fcb-a2dc-4bd8-a6c7-54453e49e01b

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_dual_le_weyl
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_zerol
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_hw_rad
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_rad_rowDiv
import Theorems.Thm_Formalism_GradedWeylDivisibility_applyWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}
namespace Formalism.BranchingDeterminantCap.BsForm
theorem _root_.solution (H : BsForm sg D) (hsg : Antitone sg)
    (h0 : D (hw ℂ le_rfl sg) (hw ℂ le_rfl sg) = 0) :
    ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg, D p q = 0 := by
  have W : ∀ w : List (Fin n × Fin n × ℕ), applyWord ℂ w (hw ℂ le_rfl sg) ∈ dualWeyl ℂ n n sg ∧
      ∀ q ∈ dualWeyl ℂ n n sg, D (applyWord ℂ w (hw ℂ le_rfl sg)) q = 0 := by
    intro w
    induction w with
    | nil => exact ⟨hwMem ℂ n n le_rfl sg hsg, H.hw_rad hsg h0⟩
    | cons x w ih =>
      rw [applyWord_cons]
      exact ⟨rowDivStable ℂ n n sg _ _ _ _ ih.1, H.rad_rowDiv _ ih.1 ih.2 _ _ _⟩
  intro p hp q hq
  have key : ∀ p ∈ weyl ℂ n n le_rfl sg, D p q = 0 := by
    intro p hp'
    unfold weyl at hp'
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact (W w).2 q hq
    | zero => exact H.zerol q
    | add x y _ _ hx hy => rw [H.addl, hx, hy, add_zero]
    | smul c x _ hx => rw [H.smull, hx, mul_zero]
  exact key p (bs_dual_le_weyl le_rfl sg hsg hp)
end Formalism.BranchingDeterminantCap.BsForm
