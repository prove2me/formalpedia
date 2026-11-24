-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.hw_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:01.776794+00:00
-- url     : https://prove2.me/submissions/4b2d7b09-81bb-48ac-80aa-dad53ed9e4e3

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_Ico_tsub_telescope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) :
    (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) = ν := by
  have hg : ∀ i, extNu ν (i + 1) ≤ extNu ν i := by
    intro i
    unfold extNu
    by_cases h1 : i + 1 < n
    · have h0 : i < n := by omega
      rw [dif_pos h1, dif_pos h0]
      exact hν (show (⟨i, h0⟩ : Fin n) ≤ ⟨i + 1, h1⟩ from Fin.mk_le_mk.mpr (Nat.le_succ i))
    · rw [dif_neg h1]
      exact Nat.zero_le _
  have hz : ∀ i, n ≤ i → extNu ν i = 0 := by
    intro i hi
    have h0 : ¬ i < n := by omega
    unfold extNu
    rw [dif_neg h0]
  funext t
  have key : ∀ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t =
      (if t.val ≤ s.val then extNu ν s.val - extNu ν (s.val + 1) else 0) := by
    intro s
    have h1 : ν s = extNu ν s.val := by
      unfold extNu
      rw [dif_pos s.isLt]
    have h2 : nuNext ν s = extNu ν (s.val + 1) := rfl
    unfold initW
    rw [h1, h2]
    by_cases hts : t.val ≤ s.val
    · have h3 : t.val < s.val + 1 := by omega
      simp only [hts, h3, if_true, mul_one]
    · have h3 : ¬ t.val < s.val + 1 := by omega
      simp only [hts, h3, if_false, mul_zero]
  have hsum : ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t
      = ∑ i ∈ Finset.range n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun s _ => key s)
  calc (∑ s : Fin n, (ν s - nuNext ν s) • initW n (s.val + 1)) t
      = ∑ s : Fin n, (ν s - nuNext ν s) * initW n (s.val + 1) t := by
        rw [Finset.sum_apply]
        rfl
    _ = ∑ i ∈ Finset.range n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) := hsum
    _ = ∑ i ∈ Finset.range t.val,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) +
        ∑ i ∈ Finset.Ico t.val n,
          (if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0) :=
        (Finset.sum_range_add_sum_Ico
          (fun i => if t.val ≤ i then extNu ν i - extNu ν (i + 1) else 0)
          (le_of_lt t.isLt)).symm
    _ = 0 + ∑ i ∈ Finset.Ico t.val n, (extNu ν i - extNu ν (i + 1)) := by
        congr 1
        · refine Finset.sum_eq_zero (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h0 : ¬ t.val ≤ i := by omega
          exact if_neg h0
        · exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_Ico.mp hi).1)
    _ = extNu ν t.val := by
        rw [zero_add]
        exact sum_Ico_tsub_telescope _ n hg hz (n - t.val) t.val rfl
    _ = ν t := by
        unfold extNu
        rw [dif_pos t.isLt]
end Formalism.GradedWeylDivisibility
