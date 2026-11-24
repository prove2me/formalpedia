-- Prove2me | solution 1 for DeletedPrimes.summable_units
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:04:31.824801+00:00
-- url     : https://prove2.me/submissions/26d0a6ae-daca-42a5-af7c-c6ab1e0147e9

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_summable_units_of_summable
import Theorems.Thm_DeletedPrimes_dim_set_two_mem

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {σ : ℝ} (hσ : dim S < σ) :
    Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) := by
  obtain ⟨σ₀, ⟨hσ₀0, hσ₀⟩, hlt⟩ := exists_lt_of_csInf_lt ⟨2, dim_set_two_mem S⟩ hσ
  have hσ0 : 0 < σ := lt_of_le_of_lt hσ₀0 hlt
  refine summable_units_of_summable (hσ₀.of_nonneg_of_le (fun n =>
    Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n) fun n => ?_)
  by_cases hn : n ∈ S
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
      exact Real.rpow_nonneg le_rfl _
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) (by linarith)
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]
end DeletedPrimes
