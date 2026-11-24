-- Prove2me | solution 1 for DeletedPrimes.isMultiplicative_sfreeFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:18.627124+00:00
-- url     : https://prove2.me/submissions/85dea3e4-8f5e-45b3-bc76-b06d5b839950

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
import Theorems.Thm_DeletedPrimes_sfreeFun_apply
import Theorems.Thm_DeletedPrimes_sFree_mul_iff

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution (hS : ∀ p ∈ S, p.Prime) : (sfreeFun S).IsMultiplicative := by
  refine ⟨?_, fun {m n} _ => ?_⟩
  · rw [sfreeFun_apply, if_pos]
    exact ⟨one_ne_zero, fun p hp hdvd => (hS p hp).one_lt.ne' (Nat.dvd_one.mp hdvd)⟩
  · simp only [sfreeFun_apply, sFree_mul_iff hS, mul_ne_zero_iff]
    by_cases hm : m ≠ 0 ∧ SFree S m <;> by_cases hn : n ≠ 0 ∧ SFree S n
    · rw [if_pos hm, if_pos hn, if_pos ⟨⟨hm.1, hn.1⟩, hm.2, hn.2⟩, mul_one]
    · rw [if_pos hm, if_neg hn, if_neg (fun h' => hn ⟨h'.1.2, h'.2.2⟩), mul_zero]
    · rw [if_neg hm, if_neg (fun h' => hm ⟨h'.1.1, h'.2.1⟩), zero_mul]
    · rw [if_neg hm, if_neg (fun h' => hm ⟨h'.1.1, h'.2.1⟩), zero_mul]
end DeletedPrimes
