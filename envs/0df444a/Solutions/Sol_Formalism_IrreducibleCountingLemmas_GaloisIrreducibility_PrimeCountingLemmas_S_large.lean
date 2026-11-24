-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.S_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:59:38.529705+00:00
-- url     : https://prove2.me/submissions/ba9e9384-bdef-4282-814a-af56958664b8

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_upper_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution (N : ℕ) (hN : 20000 ≤ N) : 1 / (5 * Real.log N) ≤ S N := by
  obtain ⟨n, hn⟩ : ∃ n, n = N / 2 := ⟨_, rfl⟩
  have hn1 : 10000 ≤ n := by omega
  have hU := upper_card n hn1
  set F := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hF
  have hsub : upper n ⊆ F ∪ {N - 2, N - 1, N} := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hp
    have h1' := Finset.mem_range.1 h1
    by_cases h4 : p + 3 ≤ N
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h2, by omega, h4⟩)
    · refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  have hcard : (upper n).card ≤ F.card + 3 :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_le_three _))
  have hcardR : ((upper n).card : ℝ) ≤ (F.card : ℝ) + 3 := by exact_mod_cast hcard
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hS : (F.card : ℝ) / N ≤ S N := by
    have e : (F.card : ℝ) / N = ∑ _p ∈ F, (1 : ℝ) / N := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [e]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, _, _⟩ := Finset.mem_filter.1 hp
    have h1' : p ≤ N := by have := Finset.mem_range.1 h1; omega
    exact one_div_le_one_div_of_le (by exact_mod_cast h2.pos) (by exact_mod_cast h1')
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn1
  have h2nN : (2 * (n : ℝ)) ≤ N := by
    have : 2 * n ≤ N := by omega
    exact_mod_cast this
  have hN2n : (N : ℝ) ≤ 2 * n + 1 := by
    have : N ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have hL0 : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hLN : Real.log (2 * n) ≤ Real.log N := Real.log_le_log (by linarith) h2nN
  have hc0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have h1 : 5 * (((upper n).card : ℝ) - 3) * Real.log (2 * n) ≤ 5 * (F.card : ℝ) * Real.log (2 * n) :=
    mul_le_mul_of_nonneg_right (by linarith) hL0.le
  have h2 : 5 * (F.card : ℝ) * Real.log (2 * n) ≤ 5 * (F.card : ℝ) * Real.log N :=
    mul_le_mul_of_nonneg_left hLN (by linarith)
  refine le_trans ?_ hS
  rw [div_le_div_iff₀ (by linarith) hNpos]
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
