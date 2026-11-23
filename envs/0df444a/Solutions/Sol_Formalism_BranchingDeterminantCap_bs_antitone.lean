-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:05.203519+00:00
-- url     : https://prove2.me/submissions/ed7eb046-00f4-4ce7-a365-b0c98310cba6

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} (lam sg : Fin n → ℕ) (h : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    Antitone sg := by
  have step : ∀ (a b : Fin n), b.val = a.val + 1 → sg b ≤ sg a := by
    intro a b hab
    have h1 := (h a).2
    have h2 := (h b).1
    have e : (a.succ : Fin (n + 1)) = b.castSucc := by
      ext; simp [hab]
    rw [e] at h1
    have : (sg b : ℤ) ≤ sg a := le_trans h2 h1
    exact_mod_cast this
  have all : ∀ (k : ℕ) (a b : Fin n), b.val = a.val + k → sg b ≤ sg a := by
    intro k
    induction k with
    | zero =>
      intro a b hab
      have : a = b := by ext; omega
      rw [this]
    | succ k ih =>
      intro a b hab
      have hlt : a.val + k < n := by have := b.isLt; omega
      exact le_trans (step ⟨a.val + k, hlt⟩ b (by simp; omega)) (ih a ⟨a.val + k, hlt⟩ rfl)
  intro a b hab
  exact all (b.val - a.val) a b (by have : a.val ≤ b.val := hab; omega)
end Formalism.BranchingDeterminantCap
