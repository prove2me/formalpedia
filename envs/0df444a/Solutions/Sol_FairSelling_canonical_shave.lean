-- Prove2me | solution 1 for FairSelling.canonical_shave
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:23.300915+00:00
-- url     : https://prove2.me/submissions/aa10e545-27f5-4ca3-9742-e2d3f61174cf

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
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
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G}
    {money : Fin 3 → ℝ} {lo : Fin 3} (hcan : IsCanonicalStrict w p τ kept sold money lo) :
    ∃ money' : Fin 3 → ℝ, IsCanonicalStrict w p τ kept sold money' lo ∧
      (∀ k, k ≠ lo → money' k = 0 ∨ vbarSum w p (kept k) + money' k = τ) ∧
      (∀ k, k ≠ lo → money' k ≤ money k) ∧ money lo ≤ money' lo := by
  classical
  obtain ⟨⟨hdisj, hsold, hm0, hmsum, hacc, hpure⟩, hcard, hstrict⟩ := hcan
  set s : Fin 3 → ℝ := fun k => min (money k) (max 0 (τ - vbarSum w p (kept k))) with hs
  have hsdef : ∀ k, s k = min (money k) (max 0 (τ - vbarSum w p (kept k))) := fun k => rfl
  have hs0 : ∀ k, 0 ≤ s k := fun k => le_min (hm0 k) (le_max_left _ _)
  have hsle : ∀ k, s k ≤ money k := fun k => min_le_left _ _
  have hsexact : ∀ k, s k = 0 ∨ vbarSum w p (kept k) + s k = τ := by
    intro k
    rcases le_or_gt τ (vbarSum w p (kept k)) with h | h
    · left
      rw [hsdef k, max_eq_left (by linarith)]
      exact min_eq_right (hm0 k)
    · right
      have hmk : τ - vbarSum w p (kept k) ≤ money k := by linarith [hacc k]
      rw [hsdef k, max_eq_right (by linarith), min_eq_right hmk]
      ring
  have hsacc : ∀ k, τ ≤ vbarSum w p (kept k) + s k := by
    intro k
    rcases hsexact k with h | h
    · rcases le_or_gt τ (vbarSum w p (kept k)) with h' | h'
      · linarith [hs0 k]
      · exfalso
        have hmk : τ - vbarSum w p (kept k) ≤ money k := by linarith [hacc k]
        rw [hsdef k, max_eq_right (by linarith), min_eq_right hmk] at h
        linarith
    · linarith
  set E : ℝ := ∑ j ∈ Finset.univ.erase lo, (money j - s j) with hE
  have hEnn : 0 ≤ E := Finset.sum_nonneg (fun j _ => by linarith [hsle j])
  set money' : Fin 3 → ℝ := fun k => if k = lo then money lo + E else s k with hmoney'
  have hlo : money' lo = money lo + E := by simp [hmoney']
  have hne : ∀ k, k ≠ lo → money' k = s k := by intro k hk; simp [hmoney', hk]
  refine ⟨money', ⟨⟨hdisj, hsold, ?_, ?_, ?_, ?_⟩, hcard, ?_⟩, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = lo
    · rw [hk, hlo]; linarith [hm0 lo]
    · rw [hne k hk]; exact hs0 k
  · have hsplit : ∑ k, money' k = ∑ k, money k := by
      rw [← Finset.add_sum_erase _ money' (Finset.mem_univ lo),
        ← Finset.add_sum_erase _ money (Finset.mem_univ lo)]
      have h1 : ∑ j ∈ Finset.univ.erase lo, money' j = ∑ j ∈ Finset.univ.erase lo, s j :=
        Finset.sum_congr rfl (fun j hj => hne j (Finset.ne_of_mem_erase hj))
      rw [h1, hlo, hE, add_assoc, ← Finset.sum_add_distrib]
      have h2 : ∑ j ∈ Finset.univ.erase lo, (money j - s j + s j)
          = ∑ j ∈ Finset.univ.erase lo, money j :=
        Finset.sum_congr rfl (fun j _ => by ring)
      rw [h2]
    rw [hsplit]; exact hmsum
  · intro k
    by_cases hk : k = lo
    · rw [hk, hlo]; linarith [hacc lo]
    · rw [hne k hk]; exact hsacc k
  · intro k hk
    rcases hpure k hk with h | h
    · exact Or.inl (by rw [hne k hk]; exact le_antisymm (by rw [← h]; exact hsle k) (hs0 k))
    · exact Or.inr h
  · intro k hk
    rcases hstrict k hk with h | ⟨hc, f, hf, hfp, hfprice⟩
    · exact Or.inl (by rw [hne k hk]; exact le_antisymm (by rw [← h]; exact hsle k) (hs0 k))
    · exact Or.inr ⟨hc, f, hf, by rw [hne k hk]; exact (hsle k).trans hfp, hfprice⟩
  · intro k hk; rw [hne k hk]; exact hsexact k
  · intro k hk; rw [hne k hk]; exact hsle k
  · rw [hlo]; linarith
end FairSelling
