-- Prove2me | solution 1 for Erdos624.proper_hole_packing
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:43.015322+00:00
-- url     : https://prove2.me/submissions/9cfd2df5-4182-4bcf-a260-d60a19c8e7c9

import Mathlib

namespace Erdos624

open Finset

lemma ph_choose_succ_ge_aux (e : ℕ) : ∀ q : ℕ, e + 1 ≤ (q + 1 + e).choose (q + 1)
  | 0 => by simp [Nat.choose_one_right]
  | q + 1 => by
    have ih := ph_choose_succ_ge_aux e q
    have h : (q + 1 + 1 + e).choose (q + 1 + 1)
        = (q + 1 + e).choose (q + 1) + (q + 1 + e).choose (q + 1 + 1) := by
      rw [show q + 1 + 1 + e = (q + 1 + e) + 1 by omega, Nat.choose_succ_succ]
    omega

/-- `C(d, q+1) + q ≥ d`. -/
lemma ph_choose_add_ge (d q : ℕ) : d ≤ d.choose (q + 1) + q := by
  rcases Nat.lt_or_ge q d with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, d = q + 1 + e := ⟨d - (q + 1), by omega⟩
    have := ph_choose_succ_ge_aux e q
    omega
  · omega

/-- **Joint proper-hole packing lemma** (capacity `q`). Let `L : Finset U → Finset C` be a list
system with `|L A| ≤ q`, `V` a pool of size `N`, and `a ≥ 1` with `N > (k-1) C((q+1)a, q+1)`.
If `(q+1)a` distinct colours `u i` have proper holes `T i ⊆ V` (no input `A ⊆ T i` with
`|A| < k` carries `u i`) with `a |T i| ≥ N`, then some `k`-subset `Y ⊆ V` misses one of these
colours: `u i ∉ ⋃_{A ⊆ Y} L A`. -/
theorem proper_hole_packing {U C : Type*} [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k a : ℕ) (V : Finset U)
    (hq : ∀ A, (L A).card ≤ q) (ha : 1 ≤ a)
    (hN : (k - 1) * ((q + 1) * a).choose (q + 1) < V.card)
    (u : Fin ((q + 1) * a) → C) (hu : Function.Injective u)
    (T : Fin ((q + 1) * a) → Finset U) (hTV : ∀ i, T i ⊆ V)
    (hhole : ∀ i, ∀ A ⊆ T i, A.card < k → u i ∉ L A)
    (hsize : ∀ i, V.card ≤ a * (T i).card) :
    ∃ Y ∈ V.powersetCard k, ∃ i, u i ∉ Y.powerset.biUnion L := by
  classical
  set N := V.card
  -- degrees
  set d : U → ℕ := fun x => (univ.filter (fun i : Fin ((q + 1) * a) => x ∈ T i)).card
  -- Step A: Σ_x d_x = Σ_i |T i|
  have hA : ∑ x ∈ V, d x = ∑ i : Fin ((q + 1) * a), (T i).card := by
    simp only [d, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hTV i h, h⟩⟩
  -- Step B: (q+1) N ≤ Σ_i |T i|
  have hB : (q + 1) * N ≤ ∑ i : Fin ((q + 1) * a), (T i).card := by
    have h1 : ∑ _i : Fin ((q + 1) * a), N ≤ ∑ i : Fin ((q + 1) * a), a * (T i).card :=
      Finset.sum_le_sum (fun i _ => hsize i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      at h1
    have h2 : a * ((q + 1) * N) ≤ a * ∑ i : Fin ((q + 1) * a), (T i).card := by
      calc a * ((q + 1) * N) = (q + 1) * a * N := by ring
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  -- Step C: Σ_x C(d_x, q+1) ≥ N
  have hC : N ≤ ∑ x ∈ V, (d x).choose (q + 1) := by
    have h1 : ∑ x ∈ V, d x ≤ ∑ x ∈ V, ((d x).choose (q + 1) + q) :=
      Finset.sum_le_sum (fun x _ => ph_choose_add_ge (d x) q)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at h1
    have : (q + 1) * N = N + q * N := by ring
    have h3 : V.card * q = q * N := by simp [N, mul_comm]
    omega
  -- Step D: double count
  have hD : ∑ x ∈ V, (d x).choose (q + 1)
      = ∑ I ∈ (univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1),
          (V.filter (fun x => ∀ i ∈ I, x ∈ T i)).card := by
    have hx : ∀ x, (d x).choose (q + 1)
        = ∑ I ∈ (univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1),
            if (∀ i ∈ I, x ∈ T i) then 1 else 0 := by
      intro x
      rw [Finset.sum_boole, Nat.cast_id, ← Finset.card_powersetCard]
      congr 1
      ext I
      simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_iff,
        Finset.mem_univ, true_and, implies_true]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    simp only [hx]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    rw [Finset.card_filter]
  -- Step E: some (q+1)-intersection has ≥ k points
  have hE : ∃ I ∈ (univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1),
      k ≤ (V.filter (fun x => ∀ i ∈ I, x ∈ T i)).card := by
    by_contra hcon
    push Not at hcon
    have h1 := Finset.sum_le_card_nsmul ((univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1))
      (fun I => (V.filter (fun x => ∀ i ∈ I, x ∈ T i)).card) (k - 1)
      (fun I hI => by have := hcon I hI; omega)
    rw [smul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
    have : ((q + 1) * a).choose (q + 1) * (k - 1) = (k - 1) * ((q + 1) * a).choose (q + 1) :=
      mul_comm _ _
    omega
  obtain ⟨I, hI, hIk⟩ := hE
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq hIk
  have hYV : Y ⊆ V := hYsub.trans (Finset.filter_subset _ _)
  have hYT : ∀ i ∈ I, Y ⊆ T i := by
    intro i hi x hx
    exact (Finset.mem_filter.1 (hYsub hx)).2 i hi
  refine ⟨Y, Finset.mem_powersetCard.2 ⟨hYV, hYcard⟩, ?_⟩
  by_contra hall
  push Not at hall
  -- every colour u i (i ∈ I) sits on the top input Y
  have htop : I.image u ⊆ L Y := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨A, hA, huA⟩ := Finset.mem_biUnion.1 (hall i)
    rw [Finset.mem_powerset] at hA
    by_cases hAY : A = Y
    · exact hAY ▸ huA
    · exfalso
      have hss : A ⊂ Y := Finset.ssubset_iff_subset_ne.2 ⟨hA, hAY⟩
      have hcard : A.card < k := hYcard ▸ Finset.card_lt_card hss
      exact hhole i A (hA.trans (hYT i hi)) hcard huA
  have h1 := Finset.card_le_card htop
  rw [Finset.card_image_of_injective _ hu, (Finset.mem_powersetCard.1 hI).2] at h1
  have := hq Y
  omega

end Erdos624

open Finset

theorem solution {U C : Type*} [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k a : ℕ) (V : Finset U)
    (hq : ∀ A, (L A).card ≤ q) (ha : 1 ≤ a)
    (hN : (k - 1) * ((q + 1) * a).choose (q + 1) < V.card)
    (u : Fin ((q + 1) * a) → C) (hu : Function.Injective u)
    (T : Fin ((q + 1) * a) → Finset U) (hTV : ∀ i, T i ⊆ V)
    (hhole : ∀ i, ∀ A ⊆ T i, A.card < k → u i ∉ L A)
    (hsize : ∀ i, V.card ≤ a * (T i).card) :
    ∃ Y ∈ V.powersetCard k, ∃ i, u i ∉ Y.powerset.biUnion L :=
  Erdos624.proper_hole_packing L q k a V hq ha hN u hu T hTV hhole hsize
