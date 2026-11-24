-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.BsForm.hw_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:09.738345+00:00
-- url     : https://prove2.me/submissions/2ed405b0-c53a-4d5a-8edc-5540918caac9

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowActDiagWeight
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
open Formalism.BranchingDeterminantCap.BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}
namespace Formalism.BranchingDeterminantCap.BsForm
theorem _root_.solution (H : BsForm sg D) (hsg : Antitone sg) (μ : Fin n → ℕ) (hμ : μ ≠ sg)
    (q : MvPolynomial (Fin n × Fin n) ℂ) (hq : q ∈ dualWeyl ℂ n n sg)
    (hqw : IsWeightedHomogeneous (rowW n n) q μ) : D (hw ℂ le_rfl sg) q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin n → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin n → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have hnu : rowNu (r := n) sg = sg := by
    funext b
    simp [rowNu]
  have hhw : IsWeightedHomogeneous (rowW n n) (hw ℂ le_rfl sg) sg := by
    have := hwRowWeight ℂ n n le_rfl sg hsg
    rwa [hnu] at this
  have hconj : (Matrix.diagonal t).conjTranspose = Matrix.diagonal t := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext b
    by_cases hb : b = a <;> simp [t, hb]
  have e := H.adj (Matrix.diagonal t) _ (hwMem ℂ n n le_rfl sg hsg) q hq
  rw [hconj, rowActDiagWeight ℂ n n t sg _ hhw, rowActDiagWeight ℂ n n t μ _ hqw, hprod, hprod,
    H.smull, H.smulr] at e
  have hstar : star ((2 : ℂ) ^ μ a) = 2 ^ μ a := by simp
  rw [hstar] at e
  have hne : (2 : ℂ) ^ sg a - 2 ^ μ a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ sg a = 2 ^ μ a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h').symm
  have : ((2 : ℂ) ^ sg a - 2 ^ μ a) * D (hw ℂ le_rfl sg) q = 0 := by rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne
end Formalism.BranchingDeterminantCap.BsForm
