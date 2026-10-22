-- Prove2me | solution 1 for ConstrNestedLogit.Card.greedy_solves_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:59:41.08375+00:00
-- url     : https://prove2.me/submissions/db12b9e4-894e-48ca-9111-ce868b84404e

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Card_Knapsack

set_option autoImplicit false

open NestedLogitVariants.LP ConstrNestedLogit.Card

theorem solution {ι : Type*} {n : ℕ} (I : Instance ι n) (c : ι → ℕ) (i : ι) (u : ℝ)
    (S : Finset (Fin n)) (hcard : S.card ≤ c i)
    (hpos : ∀ j ∈ S, 0 < utility I i j u)
    (horder : ∀ j ∈ S, ∀ k ∉ S, utility I i k u ≤ utility I i j u)
    (hrest : S.card < c i → ∀ k ∉ S, utility I i k u ≤ 0) :
    IsKnapsackOptimal I c i u S := by
  refine ⟨hcard, fun S' hS' => ?_⟩
  unfold knapsackValue
  set f : Fin n → ℝ := fun j => utility I i j u with hf
  have e1 : ∑ j ∈ S', f j = ∑ j ∈ S' ∩ S, f j + ∑ j ∈ S' \ S, f j :=
    (Finset.sum_inter_add_sum_sdiff S' S f).symm
  have e2 : ∑ j ∈ S, f j = ∑ j ∈ S ∩ S', f j + ∑ j ∈ S \ S', f j :=
    (Finset.sum_inter_add_sum_sdiff S S' f).symm
  rw [Finset.inter_comm S S'] at e2
  suffices h : ∑ j ∈ S' \ S, f j ≤ ∑ j ∈ S \ S', f j by linarith
  have hSpos : 0 ≤ ∑ j ∈ S \ S', f j :=
    Finset.sum_nonneg (fun j hj => (hpos j (Finset.mem_sdiff.1 hj).1).le)
  by_cases hlt : S.card < c i
  · have : ∑ j ∈ S' \ S, f j ≤ 0 :=
      Finset.sum_nonpos (fun k hk => hrest hlt k (Finset.mem_sdiff.1 hk).2)
    linarith
  · have hceq : S.card = c i := le_antisymm hcard (not_lt.1 hlt)
    have c1 := Finset.card_sdiff_add_card_inter S' S
    have c2 := Finset.card_sdiff_add_card_inter S S'
    rw [Finset.inter_comm S S'] at c2
    have hcc : (S' \ S).card ≤ (S \ S').card := by omega
    rcases (S' \ S).eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using hSpos
    · have hne2 : (S \ S').Nonempty := by
        rw [← Finset.card_pos] at hne ⊢; omega
      obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (S \ S') f hne2
      have hj0S : j0 ∈ S := (Finset.mem_sdiff.1 hj0).1
      have hj0pos : 0 < f j0 := hpos j0 hj0S
      have h1 : ∑ j ∈ S' \ S, f j ≤ (S' \ S).card • f j0 :=
        Finset.sum_le_card_nsmul _ _ _ (fun k hk => horder j0 hj0S k (Finset.mem_sdiff.1 hk).2)
      have h2 : (S' \ S).card • f j0 ≤ (S \ S').card • f j0 :=
        nsmul_le_nsmul_left hj0pos.le hcc
      have h3 : (S \ S').card • f j0 ≤ ∑ j ∈ S \ S', f j :=
        Finset.card_nsmul_le_sum _ _ _ hmin
      linarith
