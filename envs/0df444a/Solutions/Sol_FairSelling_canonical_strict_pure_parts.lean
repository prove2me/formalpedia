-- Prove2me | solution 1 for FairSelling.canonical_strict_pure_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:33.107008+00:00
-- url     : https://prove2.me/submissions/1f813035-96f7-41d1-aaa0-000c95bf5c64

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) {τ r : ℝ}
    (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
    (hdisjA : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hdisjs : ∀ i, Disjoint s (A i))
    (hq0 : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = ∑ g ∈ s, p g)
    (hge : ∀ i, r ≤ vbarSum w p (A i) + q i) (hscard : s.card ≤ 2)
    (lo : Fin 3) (hsmallq : ∀ i, i ≠ lo → q i ≤ r - τ) (hτr : τ ≤ r) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by
  classical
  refine ⟨A, s, fun i => if i = lo then q i else 0, lo,
    ⟨hdisjA, hdisjs, ?_, ?_, ?_, ?_⟩, hscard, ?_⟩
  · intro k; by_cases hk : k = lo <;> simp [hk, hq0]
  · have h1 : ∑ k, (if k = lo then q k else 0) = q lo := by simp
    rw [h1, ← hqsum]
    exact Finset.single_le_sum (f := q) (fun i _ => hq0 i) (Finset.mem_univ lo)
  · intro k
    by_cases hk : k = lo
    · subst hk; simpa using le_trans hτr (hge k)
    · simp only [hk, if_false, add_zero]
      have h1 := hge k
      have h2 := hsmallq k hk
      linarith
  · intro k hk; simp [hk]
  · intro k hk; simp [hk]
end FairSelling
