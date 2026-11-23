-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:30.885506+00:00
-- url     : https://prove2.me/submissions/d28d7b75-6ff7-4467-9f19-6d5d00f75c6f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution (v : M) : ∀ {m : ℕ} (g : Fin m → Module.End R M) (c : Fin m → R) (F : Fin m → Prop),
    (∀ k, F k → g k v = c k • v) → (∀ k, ¬ F k → (∀ j, k < j → F j) → g k v = 0) →
    ((∀ k, F k) → (List.ofFn g).prod v = (∏ k, c k) • v) ∧ ((¬ ∀ k, F k) → (List.ofFn g).prod v = 0)
  | 0, g, c, F, _, _ => by
    refine ⟨fun _ => by simp, fun h => absurd (fun k : Fin 0 => k.elim0) h⟩
  | m + 1, g, c, F, h1, h2 => by
    obtain ⟨ih1, ih2⟩ := solution v (fun i : Fin m => g i.succ) (fun i => c i.succ) (fun i => F i.succ)
      (fun k hk => h1 _ hk)
      (fun k hk hj => h2 _ hk (fun j hkj => by
        obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = j'.succ :=
          ⟨j.pred (by intro h; rw [h] at hkj; exact absurd hkj (Fin.not_lt_zero _)), by simp⟩
        exact hj j' (Fin.succ_lt_succ_iff.1 hkj)))
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    constructor
    · intro hF
      rw [ih1 (fun k => hF _), map_smul, h1 0 (hF 0), Fin.prod_univ_succ, smul_smul, mul_comm]
    · intro hF
      by_cases hs : ∀ k : Fin m, F k.succ
      · have h0 : ¬ F 0 := fun h0 => hF (fun k => by
          induction k using Fin.cases with
          | zero => exact h0
          | succ i => exact hs i)
        rw [ih1 hs, map_smul, h2 0 h0 (fun j hj => by
          obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = j'.succ :=
            ⟨j.pred (by intro h; rw [h] at hj; exact absurd hj (lt_irrefl _)), by simp⟩
          exact hs j'), smul_zero]
      · rw [ih2 hs, map_zero]
end Formalism.BranchingDeterminantCap
