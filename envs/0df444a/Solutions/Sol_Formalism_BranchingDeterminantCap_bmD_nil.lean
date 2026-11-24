-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:07.818071+00:00
-- url     : https://prove2.me/submissions/13a1aab4-b0de-408e-b974-226fb929f14d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_mem_dualWeyl_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_neg_eq_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_E
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_iter_Eul_l
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
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ} (lam : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) (hG : G ∈ dualWeyl R r n lam) (l j : Fin n) (hlj : l < j)
    (k : ℕ) (hk : (lam l : ℤ) - (lam j : ℤ) < (k : ℤ)) : (ndF R r n l j)^[k] G = 0 := by
  have hne : l ≠ j := ne_of_lt hlj
  have hl := (bm_mem_dualWeyl_iff.1 hG).1 l
  have hj := (bm_mem_dualWeyl_iff.1 hG).1 j
  have hE := (bm_mem_dualWeyl_iff.1 hG).2 l j hlj
  have hN : (ndF R r n l j)^[lam l + 1] G = 0 := by
    apply ndEul_neg_eq_zero l
    rw [nd_iter_Eul_l hne hl, Nat.cast_succ, show (lam l : R) - ((lam l : R) + 1) = -1 by ring,
      neg_one_smul]
  have hstep : ∀ k : ℕ, (lam l : ℤ) - (lam j : ℤ) < (k : ℤ) → (ndF R r n l j)^[k + 1] G = 0 →
      (ndF R r n l j)^[k] G = 0 := by
    intro k hk hk1
    have h1 := nd_iter_E hne hl hj hE k
    rw [hk1, map_zero] at h1
    have hc : (((k : R) + 1) * ((lam l : R) - (lam j : R) - k)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      have : (lam l : R) - (lam j : R) - k = (((lam l : ℤ) - lam j - k : ℤ) : R) := by
        push_cast; ring
      rw [this, Int.cast_ne_zero]
      omega
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  have hdown : ∀ e k : ℕ, (lam l : ℤ) - (lam j : ℤ) < (k : ℤ) → (ndF R r n l j)^[k + e] G = 0 →
      (ndF R r n l j)^[k] G = 0 := by
    intro e
    induction e with
    | zero => intro k _ hk0; simpa using hk0
    | succ e ih =>
      intro k hk hk0
      refine hstep k hk (ih (k + 1) (by push_cast; omega) ?_)
      rw [show k + 1 + e = k + (e + 1) by omega]
      exact hk0
  refine hdown (lam l + 1) k hk ?_
  rw [Function.iterate_add_apply, hN]
  exact Function.iterate_fixed (map_zero _) k
end Formalism.BranchingDeterminantCap
