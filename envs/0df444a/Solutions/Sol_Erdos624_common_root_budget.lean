-- Prove2me | solution 1 for Erdos624.common_root_budget
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:43.505992+00:00
-- url     : https://prove2.me/submissions/2c047054-2f34-4a08-9a95-c52ca69952ba

import Mathlib

namespace Erdos624

open Finset

/-- **Common-root budget for top-only repairs.** Capacity-2 list system `L`, pool `V`,
root `W ⊆ V` with `|W| = k - 1`, and every `k`-subset of `V` covering all colours. For a colour
`u` missed by `W`, let `B_u = {x ∈ V \ W : u ∉ J°(W ∪ {x})}`, where `J°(Y)` is the palette of
the proper subsets of `Y`. Then `Σ_{u ∉ J(W)} |B_u| ≤ 2 (N - k + 1)`. -/
theorem common_root_budget {U C : Type*} [DecidableEq U] [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (V W : Finset U) (hWV : W ⊆ V)
    (hW : W.card = k - 1) (hq : ∀ A, (L A).card ≤ 2)
    (hcov : ∀ Y ∈ V.powersetCard k, ∀ u : C, u ∈ Y.powerset.biUnion L) :
    ∑ u ∈ univ \ W.powerset.biUnion L,
        ((V \ W).filter (fun x =>
          u ∉ ((insert x W).powerset.filter (fun A => A ≠ insert x W)).biUnion L)).card
      ≤ 2 * (V.card + 1 - k) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have hx : ∀ x ∈ V \ W, (∑ u ∈ univ \ W.powerset.biUnion L,
      if u ∉ ((insert x W).powerset.filter (fun A => A ≠ insert x W)).biUnion L then 1 else 0)
      ≤ 2 := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [← Finset.card_filter]
    refine le_trans (Finset.card_le_card ?_) (hq (insert x W))
    intro u hu
    rw [Finset.mem_filter] at hu
    have hY : insert x W ∈ V.powersetCard k := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.insert_subset hx.1 hWV, ?_⟩
      rw [Finset.card_insert_of_notMem hx.2, hW]; omega
    obtain ⟨A, hA, huA⟩ := Finset.mem_biUnion.1 (hcov _ hY u)
    by_cases hAY : A = insert x W
    · exact hAY ▸ huA
    · exact absurd (Finset.mem_biUnion.2 ⟨A, Finset.mem_filter.2 ⟨hA, hAY⟩, huA⟩) hu.2
  refine (Finset.sum_le_card_nsmul _ _ 2 hx).trans (le_of_eq ?_)
  rw [smul_eq_mul, Finset.card_sdiff_of_subset hWV, hW, mul_comm]
  congr 1
  omega

end Erdos624

open Finset

theorem solution {U C : Type*} [DecidableEq U] [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (V W : Finset U) (hWV : W ⊆ V)
    (hW : W.card = k - 1) (hq : ∀ A, (L A).card ≤ 2)
    (hcov : ∀ Y ∈ V.powersetCard k, ∀ u : C, u ∈ Y.powerset.biUnion L) :
    ∑ u ∈ univ \ W.powerset.biUnion L,
        ((V \ W).filter (fun x =>
          u ∉ ((insert x W).powerset.filter (fun A => A ≠ insert x W)).biUnion L)).card
      ≤ 2 * (V.card + 1 - k) :=
  Erdos624.common_root_budget L k hk V W hWV hW hq hcov
