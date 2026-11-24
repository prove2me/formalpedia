-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.chk_sound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:56.779872+00:00
-- url     : https://prove2.me/submissions/76877575-7734-425d-ad10-f407a20d7836

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_test_spec
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_PrimeCountingLemmas_bsum_eq

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
theorem _root_.solution {M F r a b : ℕ} (hM : 0 < M) (hF : F = r.factorial)
    (h : chk M F r a b = true) (N : ℕ)
    (haN : a ≤ N) (hNb : N ≤ b) : (1 : ℝ) / 20 ≤ S N := by
  simp only [chk, Nat.ble_eq] at h
  rw [bsum_eq] at h
  generalize Finset.Ico (b / 2) (b / 2 + 2 ^ Nat.log2 a) = I at h
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (M : ℝ) ≤ 20 * ∑ p ∈ I, (term M F r a b p : ℝ) := by
    exact_mod_cast h
  have h2 : ∑ p ∈ I, (term M F r a b p : ℝ) ≤ M * S N := by
    unfold S
    rw [Finset.mul_sum]
    have e : ∀ p, (term M F r a b p : ℝ) =
        if test F r a b p = true then ((M / p : ℕ) : ℝ) else 0 := by
      intro p; unfold term; cases test F r a b p <;> simp
    simp only [e]
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_sum (fun p _ => (Nat.cast_div_le : ((M / p : ℕ) : ℝ) ≤ M / p))).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (t := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N))
      ?_ ?_).trans (le_of_eq ?_)
    · intro p hp
      obtain ⟨h3, h4, h5⟩ := test_spec hF (Finset.mem_filter.mp hp).2
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h3, by omega, by omega⟩
    · intro p _ _; positivity
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
  have h4 : (1 : ℝ) ≤ 20 * S N := by
    by_contra hc
    have := mul_lt_mul_of_pos_left (not_le.mp hc) hMr
    linarith
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
