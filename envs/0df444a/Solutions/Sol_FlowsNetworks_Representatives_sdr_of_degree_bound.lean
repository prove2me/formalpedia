-- Prove2me | solution 1 for FlowsNetworks.Representatives.sdr_of_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:36:40.410682+00:00
-- url     : https://prove2.me/submissions/c77a99be-688b-4345-8138-adcfd49c9a35

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives
open FlowsNetworks.Representatives


theorem g69e_double_count {m n : ℕ} (S : Fin n → Finset (Fin m)) (X : Finset (Fin n)) :
    ∑ j ∈ X, (S j).card ≤ ∑ i ∈ X.biUnion S, (Finset.univ.filter (fun j => i ∈ S j)).card := by
  have h1 : ∀ j ∈ X, (S j).card = ∑ i ∈ X.biUnion S, if i ∈ S j then 1 else 0 := by
    intro j hj
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext i; simp only [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨fun h => ⟨⟨j, hj, h⟩, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_boole, Nat.cast_id]
  apply Finset.card_le_card
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.2


/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 10.2 (p. 58). Let `S_j` contain
`s j` elements (`j = 1, …, n`), let `eᵢ` occur in `r i` of the sets `S_j` (`i = 1, …, m`), let
`𝕊 = ∑ⱼ s j` and `M = max(r₁, …, r_m, s₁, …, s_n)`. If `(n − 1) M < 𝕊`, then `𝒮` has an SDR.
(The page prints the maximum over `r₁, …, r_n`; the `r`'s are indexed by `i = 1, …, m`, and the
maximum is taken over all of them.) -/
theorem solution {m n : ℕ} (S : Fin n → Finset (Fin m))
    (s : Fin n → ℕ) (hs : ∀ j, s j = (S j).card)
    (r : Fin m → ℕ) (hr : ∀ i, r i = (Finset.univ.filter (fun j => i ∈ S j)).card)
    (M : ℕ) (hM : M = max (Finset.univ.sup r) (Finset.univ.sup s))
    (hlt : ((n : ℤ) - 1) * (M : ℤ) < ∑ j, (s j : ℤ)) :
    ∃ f : Fin n → Fin m, IsSDR S f := by
  have hrM : ∀ i, r i ≤ M := fun i => hM ▸ le_max_of_le_left (Finset.le_sup (Finset.mem_univ i))
  have hsM : ∀ j, s j ≤ M := fun j => hM ▸ le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))
  have hall : ∀ X : Finset (Fin n), X.card ≤ (X.biUnion S).card := by
    intro X
    by_contra hlt2
    rw [not_le] at hlt2
    have hX : X.card ≥ 1 := by omega
    have e1 : ∑ j ∈ X, s j ≤ (X.biUnion S).card * M := by
      calc ∑ j ∈ X, s j = ∑ j ∈ X, (S j).card := Finset.sum_congr rfl fun j _ => hs j
        _ ≤ ∑ i ∈ X.biUnion S, r i := by
          refine (g69e_double_count S X).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun i _ => (hr i).symm
        _ ≤ ∑ i ∈ X.biUnion S, M := Finset.sum_le_sum fun i _ => hrM i
        _ = (X.biUnion S).card * M := by simp
    have e2 : ∑ j ∈ Xᶜ, s j ≤ Xᶜ.card * M := by
      calc ∑ j ∈ Xᶜ, s j ≤ ∑ j ∈ Xᶜ, M := Finset.sum_le_sum fun j _ => hsM j
        _ = Xᶜ.card * M := by simp
    have e3 : ∑ j, s j = ∑ j ∈ X, s j + ∑ j ∈ Xᶜ, s j := (Finset.sum_add_sum_compl X s).symm
    have hc : Xᶜ.card = n - X.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hXn : X.card ≤ n := by simpa using Finset.card_le_univ X
    have hsum : ((∑ j, s j : ℕ) : ℤ) = ∑ j, (s j : ℤ) := by push_cast; rfl
    have key : ∑ j, s j ≤ (n - 1) * M := by
      have : (X.biUnion S).card * M + Xᶜ.card * M ≤ (n - 1) * M := by
        rw [← add_mul]; apply Nat.mul_le_mul_right; omega
      omega
    have : ((∑ j, s j : ℕ) : ℤ) ≤ ((n - 1 : ℕ) : ℤ) * M := by exact_mod_cast key
    rw [hsum] at this
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      have : 1 ≤ n := le_trans hX hXn
      push_cast [this]; ring
    rw [hn1] at this
    linarith
  obtain ⟨f, hf, hfS⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective S).1 hall
  exact ⟨f, hf, hfS⟩

