-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmLift_minor1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:40.889035+00:00
-- url     : https://prove2.me/submissions/5c2020c8-3023-49a1-951c-2537bbfb7d0e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_sum
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_of_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_emb_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zW_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_lastW_castSucc
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zmon_single
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_omg_single
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_neg_one_pow_WH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_laplace
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_initMinor_mem
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s + 1 ≤ n) :
    bmLift R n (initW n (s + 1)) (Pi.single ⟨s, hs⟩ 1) (initMinor R I (Nat.le_of_succ_le hs))
      (initMinor R (fun p : Fin (s + 1) => if h : p.val < s then (I ⟨p.val, h⟩).castSucc else Fin.last n) hs) := by
  classical
  refine ⟨initMinor_mem _ hs, ?_, ?_⟩
  · rw [bmF_laplace]
    have hsum : (∑ t : Fin n, (Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℕ) t) = 1 := by
      rw [Finset.sum_eq_single (⟨s, hs⟩ : Fin n)]
      · simp
      · intro t _ ht
        simp [ht]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
    have h1 := ((bmF_neg_one_pow_WH (R := R) (lastW n) (s + (j : ℕ))).mul
      (isWeightedHomogeneous_X R (lastW n) (Fin.last n, Fin.castLE hs j))).mul
      (bmF_emb_WH (lastW n) bmF_lastW_castSucc (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det)
    simpa [lastW] using h1
  · rw [bmF_laplace, Fin.sum_univ_castSucc, bmF_zmon_single]
    have hlast : (-1 : BP R n) ^ (s + ((Fin.last s : Fin (s + 1)) : ℕ)) *
        X (Fin.last n, Fin.castLE hs (Fin.last s)) *
        emb R n (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs ((Fin.last s).succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det =
        X (Fin.last n, (⟨s, hs⟩ : Fin n)) * emb R n (initMinor R I (Nat.le_of_succ_le hs)) := by
      have h1 : (-1 : BP R n) ^ (s + ((Fin.last s : Fin (s + 1)) : ℕ)) = 1 := by
        rw [Fin.val_last, ← two_mul, pow_mul]; simp
      have h2 : ∀ q : Fin s, Fin.castLE hs ((Fin.last s).succAbove q) = Fin.castLE (Nat.le_of_succ_le hs) q := by
        intro q
        rw [Fin.succAbove_last]
        rfl
      rw [h1, one_mul]
      simp only [h2]
      rfl
    rw [hlast, add_sub_cancel_right]
    refine bmF_low_sum _ _ fun j _ => ?_
    have h1 := ((bmF_neg_one_pow_WH (R := R) (zW n) (s + ((j.castSucc : Fin (s + 1)) : ℕ))).mul
      (isWeightedHomogeneous_X R (zW n) (Fin.last n, Fin.castLE hs j.castSucc))).mul
      (bmF_emb_WH (zW n) bmF_zW_castSucc (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.castSucc.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det)
    refine bmF_low_of_WH h1 ?_
    have h2 : (0 : Fin n → ℤ) + zW n (Fin.last n, Fin.castLE hs j.castSucc) + 0 =
        Pi.single (Fin.castLE hs j.castSucc) 1 := by
      simp [zW]
    have h3 : (fun t => (((Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℕ) t : ℕ) : ℤ)) =
        (Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℤ) := by
      funext t
      by_cases ht : t = ⟨s, hs⟩
      · subst ht; simp
      · simp [ht]
    rw [h2, h3, bmF_omg_single, bmF_omg_single]
    simp
end Formalism.BranchingDeterminantCap
