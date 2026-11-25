-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.xn_stage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:06.112806+00:00
-- url     : https://prove2.me/submissions/412b00e0-65a3-4e28-b9a2-252e8737d974

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_congr
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_mono
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_pow
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_rowsA_inj
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_rowsB_inj
import Theorems.Thm_Formalism_BranchingDeterminantCap_xn_interlace
import Theorems.Thm_Formalism_BranchingDeterminantCap_xnLam_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (n : ℕ) (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (k : ℕ) (hk : k ≤ n) :
    xnInv (r := n + 1) (n := n) k (fun q => xnLam lam q - xnLam lam k)
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
          initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i)))
      (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < k),
        (lpMinor ℂ (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) := by
  induction k with
  | zero =>
    refine xnInv_congr (xnInv_zero (r := n + 1) (n := n)) ?_ ?_ ?_
    · funext q
      have := xnLam_anti lam sg hI (Nat.zero_le q)
      show 0 = xnLam lam q - xnLam lam 0
      omega
    · simp
    · simp
  | succ k ih =>
    have hkn : k < n := by omega
    have H0 := xnInv_mono (ih (by omega))
    have H1 := xnInv_pow H0 hk (by omega) (rowsA ⟨k, hkn⟩) (xn_rowsA_inj _)
      (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩)
    have H2 := xnInv_pow H1 hk (by omega) (rowsB ⟨k, hkn⟩) (xn_rowsB_inj _)
      (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩)
    obtain ⟨i1, i2⟩ := xn_interlace lam sg hI ⟨k, hkn⟩
    have hf : (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
        insert ⟨k, hkn⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff,
        Fin.val_mk]
      constructor <;> intro h <;> omega
    have hnot : (⟨k, hkn⟩ : Fin n) ∉ (Finset.univ.filter fun i : Fin n => i.val < k) := by simp
    refine xnInv_congr H2 ?_ ?_ ?_
    · funext q
      have e1 : xnLam lam k = lam ⟨k, hkn⟩ := by simp [xnLam, hkn]
      have e2 : xnLam lam (k + 1) = nuNext lam ⟨k, hkn⟩ := by
        simp only [xnLam, nuNext, Fin.val_mk]
      have a1 := xnLam_anti lam sg hI (Nat.le_succ k)
      by_cases hq : q < k + 1
      · have a2 := xnLam_anti lam sg hI (show q ≤ k by omega)
        simp only [if_pos hq]
        omega
      · have a2 := xnLam_anti lam sg hI (show k + 1 ≤ q by omega)
        simp only [if_neg hq]
        omega
    · rw [hf, Finset.prod_insert hnot]
      ring
    · have hexp : (lam ⟨k, hkn⟩ - sg ⟨k, hkn⟩) + (sg ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩) =
          lam ⟨k, hkn⟩ - nuNext lam ⟨k, hkn⟩ := by omega
      rw [hf, Finset.prod_insert hnot, ← mul_assoc, ← pow_add, hexp]
end Formalism.BranchingDeterminantCap
