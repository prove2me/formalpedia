-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bad_primes_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:29.864008+00:00
-- url     : https://prove2.me/submissions/654ef8e4-5704-4520-a598-904eb366f0a5

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_bbAtMostThree
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : BBCard := by
  classical
  intro g N hg
  set T : ℕ → Finset ℕ := fun d => (Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) with hT
  have hTd : ∀ d ∈ Finset.Icc 1 N, (T d).card ≤ 3 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    apply Formalism.GaloisIrreducibility.bbAtMostThree g d (T d) hg hd.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      exact hl.2.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      have h1 : g ^ d < (l ^ padicValNat l (g ^ d - 1)) ^ 4 := by
        rw [← pow_mul, mul_comm]; exact hl.2.2
      have h2 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 = (g : ℝ) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = (d : ℝ) := by push_cast; ring
        rw [this, Real.rpow_natCast]
      have h3 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 <
          (((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ^ 4 := by
        rw [h2]; exact_mod_cast h1
      exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h3
  have hsub : (Finset.range (g ^ N + 1)).filter (fun l =>
      l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) ⊆
      (Finset.Icc 1 N).biUnion T := by
    intro l hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hr, hp, d, hd, hlt⟩ := hl
    rw [Finset.mem_biUnion]
    exact ⟨d, hd, by simp only [hT, Finset.mem_filter]; exact ⟨hr, hp, hlt⟩⟩
  have hcard : ((Finset.Icc 1 N).biUnion T).card ≤ 3 * N := by
    calc ((Finset.Icc 1 N).biUnion T).card ≤ ∑ d ∈ Finset.Icc 1 N, (T d).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, 3 := Finset.sum_le_sum hTd
      _ = 3 * N := by simp [mul_comm]
  unfold BB
  calc _ ≤ _ + 1 := Finset.card_insert_le _ _
    _ ≤ 3 * N + 1 := by
      have := (Finset.card_le_card hsub).trans hcard
      convert Nat.add_le_add_right this 1
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
