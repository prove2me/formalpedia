-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_Pi_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:34.84763+00:00
-- url     : https://prove2.me/submissions/1b0de491-ec72-4a5d-b7ec-b176d0417978

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_Pi_adj
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one
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
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (τ : Equiv.Perm (Fin n)) :
    ∀ β : Fin n → Fin n, bmPi E u (β ∘ τ) = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • bmPi E u β := by
  cases n with
  | zero =>
    intro β
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ m =>
    have hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top _
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro β
      rw [bmA_Pi_adj E u hE h2 i.castSucc i.succ (by simp) β,
        Equiv.Perm.sign_swap (by intro h; have := congrArg Fin.val h; simp at this)]
      simp
    | one => intro β; simp
    | mul x y _ _ hx hy =>
      intro β
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, Equiv.Perm.sign_mul, smul_smul]
      congr 1
      push_cast
      ring
end Formalism.BranchingDeterminantCap
