-- Prove2me | solution 1 for Conway99.triangle_system_iff_adjacency_matrix
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-25T17:47:44.759992+00:00
-- url     : https://prove2.me/submissions/1a2ba151-1c70-4bbe-a49c-d54b0563e36e

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

set_option autoImplicit false

open scoped BigOperators

/-- If every term of a finset sum is at least 1 and the sum equals the
cardinality, every term equals 1. -/
lemma sum_eq_card_of_ge1 {α : Type*} [DecidableEq α] (f : α → ℕ) (s : Finset α)
    (h1 : ∀ x ∈ s, 1 ≤ f x) (hsum : ∑ x ∈ s, f x = s.card) :
    ∀ x ∈ s, f x = 1 := by
  intro x hx
  by_contra hne
  have h2 : 2 ≤ f x := by
    have h1x := h1 x hx
    omega
  have hsplit : ∑ x_ ∈ s, f x_ = f x + ∑ x_ ∈ s.erase x, f x_ :=
    (Finset.add_sum_erase s f hx).symm
  have hsplit1 : ∑ _x ∈ s, (1 : ℕ) = 1 + ∑ _x ∈ s.erase x, 1 := by
    have h := (Finset.add_sum_erase s (fun _ => (1 : ℕ)) hx).symm
    simpa using h
  have hle2 : ∑ _x ∈ s.erase x, (1 : ℕ) ≤ ∑ x_ ∈ s.erase x, f x_ :=
    Finset.sum_le_sum (fun i hi => h1 i (Finset.mem_of_mem_erase hi))
  have hcard : ∑ _x ∈ s, (1 : ℕ) = s.card := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  omega

/-- Backward direction: a Conway 99 line system yields the adjacency matrix. -/
lemma back_dir (L : Finset (Finset (Fin 99)))
    (h3 : ∀ l ∈ L, l.card = 3)
    (hInt : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1)
    (h7 : ∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7)
    (hμ : ∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
      (Finset.univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
          (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2) :
    ∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j = (if i = j then 12 else 0) + 2) := by
  classical
  set C : (Fin 99) → (Fin 99) → Prop :=
    fun i j => i ≠ j ∧ ∃ l ∈ L, i ∈ l ∧ j ∈ l with hC
  set A : Matrix (Fin 99) (Fin 99) ℕ :=
    fun i j => if C i j then 1 else 0 with hA
  have Csymm : ∀ i j : Fin 99, C i j → C j i := by
    intro i j h
    simp only [hC] at h ⊢
    obtain ⟨hne, l, hl, hi, hj⟩ := h
    exact ⟨Ne.symm hne, l, hl, hj, hi⟩
  have Cirrefl : ∀ i : Fin 99, ¬ C i i := by
    intro i h
    simp only [hC] at h
    exact absurd rfl h.1
  have A01 : ∀ i j : Fin 99, A i j = 0 ∨ A i j = 1 := by
    intro i j
    simp only [hA]
    by_cases h : C i j <;> simp [h]
  have Asymm : ∀ i j : Fin 99, A i j = A j i := by
    intro i j
    simp only [hA]
    by_cases h1 : C i j
    · have h2 : C j i := Csymm i j h1
      simp [h1, h2]
    · have h2 : ¬ C j i := fun h => h1 (Csymm j i h)
      simp [h1, h2]
  have Adiag : ∀ i : Fin 99, A i i = 0 := by
    intro i
    simp only [hA]
    rw [if_neg (Cirrefl i)]
  -- Every vertex has exactly 14 neighbours: the seven lines through it are
  -- pairwise disjoint away from it, each contributing two new points.
  have deg14 : ∀ i : Fin 99, (Finset.univ.filter fun k => C i k).card = 14 := by
    intro i
    have hunion : Finset.univ.filter (fun k => C i k)
        = (L.filter fun l => i ∈ l).biUnion fun l => l.erase i := by
      apply Finset.ext; intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_erase, hC]
      constructor
      · rintro ⟨hne, l, hl, hi, hk⟩
        exact ⟨l, ⟨hl, hi⟩, Ne.symm hne, hk⟩
      · rintro ⟨l, ⟨hl, hi⟩, hki, hk⟩
        exact ⟨Ne.symm hki, l, hl, hi, hk⟩
    have hdisj : ((L.filter fun l => i ∈ l) : Set (Finset (Fin 99))).PairwiseDisjoint
        fun l => l.erase i := by
      intro l₁ hl₁ l₂ hl₂ hne
      show Disjoint (l₁.erase i) (l₂.erase i)
      rw [Finset.mem_coe, Finset.mem_filter] at hl₁ hl₂
      obtain ⟨hm1, hi1⟩ := hl₁; obtain ⟨hm2, hi2⟩ := hl₂
      apply Finset.disjoint_left.mpr
      intro k hk1 hk2
      rw [Finset.mem_erase] at hk1 hk2
      obtain ⟨hki1, hk1⟩ := hk1; obtain ⟨hki2, hk2⟩ := hk2
      have hmem1 : k ∈ l₁ ∩ l₂ := Finset.mem_inter.mpr ⟨hk1, hk2⟩
      have hmem2 : i ∈ l₁ ∩ l₂ := Finset.mem_inter.mpr ⟨hi1, hi2⟩
      have hle := hInt l₁ hm1 l₂ hm2 hne
      have hlt : 1 < (l₁ ∩ l₂).card :=
        Finset.one_lt_card.mpr ⟨i, hmem2, k, hmem1, Ne.symm hki1⟩
      omega
    rw [hunion, Finset.card_biUnion hdisj]
    have h2 : ∀ l ∈ L.filter (fun l => i ∈ l), (l.erase i).card = 2 := by
      intro l hl
      rw [Finset.mem_filter] at hl
      have hcc := h3 l hl.1
      have her := Finset.card_erase_of_mem hl.2
      omega
    calc ∑ u ∈ L.filter (fun l => i ∈ l), (u.erase i).card
        = ∑ _l ∈ L.filter (fun l => i ∈ l), 2 :=
          Finset.sum_congr rfl (fun l hl => h2 l hl)
      _ = 14 := by simp [Finset.sum_const, h7 i]
  -- The square of the adjacency matrix counts common neighbours.
  have sq_cn : ∀ p q : Fin 99, (∑ k : Fin 99, A p k * A k q)
      = (Finset.univ.filter fun k => C p k ∧ C k q).card := by
    intro p q
    have hterm : ∀ k : Fin 99, A p k * A k q
        = (if C p k ∧ C k q then (1 : ℕ) else 0) := by
      intro k
      simp only [hA]
      by_cases h1 : C p k <;> by_cases h2 : C k q <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_boole, Nat.cast_id]
  -- Diagonal: common neighbours of a vertex with itself are its neighbours.
  have cn_diag : ∀ p : Fin 99, (Finset.univ.filter fun k => C p k ∧ C k p).card = 14 := by
    intro p
    have heq : Finset.univ.filter (fun k => C p k ∧ C k p)
        = Finset.univ.filter fun k => C p k := by
      apply Finset.ext; intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact h.1
      · intro h
        exact ⟨h, Csymm p k h⟩
    rw [heq]; exact deg14 p
  -- Non-adjacent pair: the two points supplied by hμ are exactly the common
  -- neighbours (each has its own line to both, and any common neighbour is
  -- one of the two since the lines through p are disjoint away from p).
  have cn_nonadj : ∀ i j : Fin 99, i ≠ j → ¬ C i j →
      (Finset.univ.filter fun k => C i k ∧ C k j).card = 2 := by
    intro i j hne hnadj
    have hnc : ∀ l ∈ L, ¬(i ∈ l ∧ j ∈ l) := by
      intro l hl hcon
      apply hnadj
      simp only [hC]
      exact ⟨hne, l, hl, hcon.1, hcon.2⟩
    have h2 := hμ i j hne hnc
    have heq : Finset.univ.filter (fun k => C i k ∧ C k j)
        = Finset.univ.filter fun z : Fin 99 => z ≠ i ∧ z ≠ j ∧
            (∃ l ∈ L, i ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, j ∈ l ∧ z ∈ l) := by
      apply Finset.ext; intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hC]
      constructor
      · rintro ⟨⟨h1, l1, hl1, hi1, hk1⟩, ⟨h2, l2, hl2, hk2, hj2⟩⟩
        exact ⟨Ne.symm h1, h2, ⟨l1, hl1, hi1, hk1⟩, ⟨l2, hl2, hj2, hk2⟩⟩
      · rintro ⟨hki, hkj, ⟨l1, hl1, hi1, hk1⟩, ⟨l2, hl2, hj2, hk2⟩⟩
        exact ⟨⟨Ne.symm hki, l1, hl1, hi1, hk1⟩, ⟨hkj, l2, hl2, hk2, hj2⟩⟩
    rw [heq]
    exact h2
  -- Every adjacent pair has at least one common neighbour: the third point
  -- of their line.
  have cn_adj_ge1 : ∀ i j : Fin 99, ∀ q ∈ (Finset.univ.erase i).filter (fun q => C i q),
      1 ≤ (Finset.univ.filter fun k => C i k ∧ C k q).card := by
    intro i j q hq
    rw [Finset.mem_filter, Finset.mem_erase] at hq
    obtain ⟨_, hadj⟩ := hq
    simp only [hC] at hadj
    obtain ⟨hne, l, hl, hi, hqmem⟩ := hadj
    have hlc := h3 l hl
    have e1 : (l.erase i).card = 2 := by
      have her := Finset.card_erase_of_mem hi
      omega
    have hq1 : q ∈ l.erase i := Finset.mem_erase.mpr ⟨Ne.symm hne, hqmem⟩
    have e2 : ((l.erase i).erase q).card = 1 := by
      have her := Finset.card_erase_of_mem hq1
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((l.erase i).erase q).card)
    rw [Finset.mem_erase] at hz
    obtain ⟨hzq, hz⟩ := hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hzi, hz⟩ := hz
    have hmem : z ∈ Finset.univ.filter fun k => C i k ∧ C k q := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ z, ?_, ?_⟩ <;> simp only [hC]
      · exact ⟨Ne.symm hzi, l, hl, hi, hz⟩
      · exact ⟨hzq, l, hl, hz, hqmem⟩
    have hpos := Finset.card_pos.mpr ⟨z, hmem⟩
    omega
  have hfib : ∀ p : Fin 99, ((Finset.univ.erase p).filter fun q => C p q).card = 14 := by
    intro p
    have heq : (Finset.univ.erase p).filter (fun q => C p q)
        = Finset.univ.filter fun q => C p q := by
      apply Finset.ext; intro q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true,
        Finset.mem_erase]
      constructor
      · intro h; exact h.2
      · intro h
        refine ⟨?_, h⟩
        intro hqp
        rw [hqp] at h
        exact absurd h (Cirrefl p)
    rw [heq]; exact deg14 p
  -- Double count of (p, q, k) with k a common neighbour of p, q.
  have sum_cn : ∑ p : Fin 99, ∑ q : Fin 99,
      (Finset.univ.filter fun k => C p k ∧ C k q).card = 99 * 196 := by
    have hrow : ∀ k : Fin 99, (∑ q : Fin 99, A k q) = 14 := by
      intro k
      have hterm : ∀ p : Fin 99, A k p = (if C k p then (1 : ℕ) else 0) := by
        intro p; simp only [hA]
      calc ∑ q : Fin 99, A k q = ∑ p : Fin 99, (if C k p then (1 : ℕ) else 0) :=
            Finset.sum_congr rfl (fun p _ => hterm p)
        _ = (Finset.univ.filter fun p => C k p).card := by
            rw [Finset.sum_boole, Nat.cast_id]
        _ = 14 := deg14 k
    have hcol : ∀ k : Fin 99, (∑ p : Fin 99, A p k) = 14 := by
      intro k
      calc ∑ p : Fin 99, A p k = ∑ p : Fin 99, A k p :=
            Finset.sum_congr rfl (fun p _ => Asymm p k)
        _ = 14 := hrow k
    calc ∑ p : Fin 99, ∑ q : Fin 99, (Finset.univ.filter fun k => C p k ∧ C k q).card
        = ∑ p : Fin 99, ∑ q : Fin 99, ∑ k : Fin 99, A p k * A k q := by
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          exact (sq_cn p q).symm
      _ = ∑ k : Fin 99, ∑ p : Fin 99, ∑ q : Fin 99, A p k * A k q := by
          calc ∑ p : Fin 99, ∑ q : Fin 99, ∑ k : Fin 99, A p k * A k q
              = ∑ p : Fin 99, ∑ k : Fin 99, ∑ q : Fin 99, A p k * A k q := by
                apply Finset.sum_congr rfl; intro p _
                exact Finset.sum_comm
            _ = ∑ k : Fin 99, ∑ p : Fin 99, ∑ q : Fin 99, A p k * A k q :=
                Finset.sum_comm
      _ = ∑ k : Fin 99, ((∑ p : Fin 99, A p k) * (∑ q : Fin 99, A k q)) := by
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_mul_sum]
      _ = 99 * 196 := by
          have h14 : ∀ k : Fin 99,
              (∑ p : Fin 99, A p k) * (∑ q : Fin 99, A k q) = 14 * 14 :=
            fun k => by rw [hcol k, hrow k]
          calc ∑ k : Fin 99, ((∑ p : Fin 99, A p k) * (∑ q : Fin 99, A k q))
              = ∑ _k : Fin 99, 14 * 14 := Finset.sum_congr rfl (fun k _ => h14 k)
            _ = 99 * 196 := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                  Nat.cast_id]
  -- Split the q-sum at p into: the diagonal (14), the neighbours (S_p),
  -- and the 84 non-neighbours (each contributing 2).
  have hsplit1 : ∀ p : Fin 99, (∑ q : Fin 99, (Finset.univ.filter fun k => C p k ∧ C k q).card)
      = 14 + (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
          (Finset.univ.filter fun k => C p k ∧ C k q).card) + 168 := by
    intro p
    have hpeel := Finset.add_sum_erase Finset.univ
      (fun q => (Finset.univ.filter fun k => C p k ∧ C k q).card) (Finset.mem_univ p)
    have hsplit2 := Finset.sum_filter_add_sum_filter_not (Finset.univ.erase p)
      (fun q => C p q)
      (fun q => (Finset.univ.filter fun k => C p k ∧ C k q).card)
    have hG : (Finset.univ.erase p).filter (fun x => ¬ (fun q => C p q) x)
        = (Finset.univ.erase p).filter fun q => ¬ C p q := by
      apply Finset.filter_congr
      intro q _
      rfl
    rw [hG] at hsplit2
    have hnonadj : (∑ q ∈ (Finset.univ.erase p).filter fun q => ¬ C p q,
        (Finset.univ.filter fun k => C p k ∧ C k q).card) = 168 := by
      have h1 : ∀ q ∈ (Finset.univ.erase p).filter fun q => ¬ C p q,
          (Finset.univ.filter fun k => C p k ∧ C k q).card = 2 := by
        intro q hq
        rw [Finset.mem_filter, Finset.mem_erase] at hq
        obtain ⟨⟨hqp, _⟩, hnC⟩ := hq
        exact cn_nonadj p q (Ne.symm hqp) hnC
      have hcard : ((Finset.univ.erase p).filter fun q => ¬ C p q).card = 84 := by
        have h1c : ((Finset.univ.erase p).filter fun q => C p q).card = 14 := hfib p
        have h2 := Finset.card_filter_add_card_filter_not (fun q => C p q)
          (s := Finset.univ.erase p)
        have hcard98 : (Finset.univ.erase p).card = 98 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
        rw [hcard98] at h2
        rw [h1c, hG] at h2
        omega
      rw [Finset.sum_congr rfl (fun q hq => h1 q hq)]
      simp [Finset.sum_const, hcard]
    rw [← hpeel, ← hsplit2, cn_diag p, hnonadj]
    ring
  -- The key double count: total common-neighbour incidences over neighbours.
  have key : (∑ p : Fin 99, ∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
      (Finset.univ.filter fun k => C p k ∧ C k q).card) = 99 * 14 := by
    have h1 := sum_cn
    have h2 : (∑ p : Fin 99, ∑ q : Fin 99, (Finset.univ.filter fun k => C p k ∧ C k q).card)
        = ∑ p : Fin 99, (14 + (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
            (Finset.univ.filter fun k => C p k ∧ C k q).card) + 168) :=
      Finset.sum_congr rfl (fun p _ => hsplit1 p)
    rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul] at h1
    simp only [Nat.cast_id] at h1
    omega
  -- Each S_p ≤ 14: otherwise the total would exceed 99 * 14.
  have Slow : ∀ p : Fin 99, (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
      (Finset.univ.filter fun k => C p k ∧ C k q).card) ≤ 14 := by
    intro p
    by_contra hlt
    have hge15 : 15 ≤ ∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
        (Finset.univ.filter fun k => C p k ∧ C k q).card := by omega
    have hbound : ∀ r : Fin 99, 14 ≤ ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
        (Finset.univ.filter fun k => C r k ∧ C k q).card := by
      intro r
      have h1 := Finset.sum_le_sum (fun q (hq : q ∈ (Finset.univ.erase r).filter fun q => C r q) =>
        cn_adj_ge1 r q q hq)
      rw [Finset.sum_const, hfib r, nsmul_eq_mul, mul_one, Nat.cast_id] at h1
      exact h1
    have htot := key
    have hsplit : (∑ r : Fin 99, ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
          (Finset.univ.filter fun k => C r k ∧ C k q).card)
        = (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
            (Finset.univ.filter fun k => C p k ∧ C k q).card)
        + ∑ r ∈ Finset.univ.erase p, ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
            (Finset.univ.filter fun k => C r k ∧ C k q).card :=
      (Finset.add_sum_erase Finset.univ
        (fun r => ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
          (Finset.univ.filter fun k => C r k ∧ C k q).card)
        (Finset.mem_univ p)).symm
    have h2 : ∑ _r ∈ Finset.univ.erase p, 14
        ≤ ∑ r ∈ Finset.univ.erase p, ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
            (Finset.univ.filter fun k => C r k ∧ C k q).card :=
      Finset.sum_le_sum (fun r _ => hbound r)
    have hcard98 : (Finset.univ.erase p).card = 98 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    have h3 : ∑ _r ∈ Finset.univ.erase p, 14 = 98 * 14 := by
      rw [Finset.sum_const, hcard98, nsmul_eq_mul, Nat.cast_id]
    omega
  -- Hence each S_p = 14.
  have key_eq : ∀ p : Fin 99, (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
      (Finset.univ.filter fun k => C p k ∧ C k q).card) = 14 := by
    intro p
    have htot := key
    have h1 := Slow p
    by_contra hne
    have hle13 : (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
        (Finset.univ.filter fun k => C p k ∧ C k q).card) ≤ 13 := by omega
    have hsplit : (∑ r : Fin 99, ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
          (Finset.univ.filter fun k => C r k ∧ C k q).card)
        = (∑ q ∈ (Finset.univ.erase p).filter fun q => C p q,
            (Finset.univ.filter fun k => C p k ∧ C k q).card)
        + ∑ r ∈ Finset.univ.erase p, ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
            (Finset.univ.filter fun k => C r k ∧ C k q).card :=
      (Finset.add_sum_erase Finset.univ
        (fun r => ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
          (Finset.univ.filter fun k => C r k ∧ C k q).card)
        (Finset.mem_univ p)).symm
    have h2 : ∑ r ∈ Finset.univ.erase p, ∑ q ∈ (Finset.univ.erase r).filter fun q => C r q,
          (Finset.univ.filter fun k => C r k ∧ C k q).card
        ≤ ∑ _r ∈ Finset.univ.erase p, 14 :=
      Finset.sum_le_sum (fun r _ => Slow r)
    have hcard98 : (Finset.univ.erase p).card = 98 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    have h3 : ∑ _r ∈ Finset.univ.erase p, 14 = 98 * 14 := by
      rw [Finset.sum_const, hcard98, nsmul_eq_mul, Nat.cast_id]
    omega
  -- Adjacent vertices have exactly one common neighbour.
  have cn_adj : ∀ i j : Fin 99, i ≠ j → C i j →
      (Finset.univ.filter fun k => C i k ∧ C k j).card = 1 := by
    intro i j hne hadj
    have h14 := key_eq i
    have hmem : j ∈ (Finset.univ.erase i).filter fun q => C i q := by
      rw [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨Ne.symm hne, Finset.mem_univ j⟩, hadj⟩
    have hsum : (∑ q ∈ (Finset.univ.erase i).filter fun q => C i q,
        (Finset.univ.filter fun k => C i k ∧ C k q).card)
        = ((Finset.univ.erase i).filter fun q => C i q).card := by
      rw [h14, hfib i]
    exact sum_eq_card_of_ge1 _ _ (fun q hq => cn_adj_ge1 i q q hq) hsum j hmem
  -- Assemble the matrix equation.
  refine ⟨A, A01, Asymm, Adiag, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Adiag i, add_zero, if_pos rfl]
    have h := sq_cn i i
    rw [cn_diag i] at h
    omega
  · rw [if_neg hij]
    by_cases hadj : C i j
    · have h1 := cn_adj i j hij hadj
      have h2 := sq_cn i j
      rw [h1] at h2
      have h3 : A i j = 1 := by simp only [hA]; rw [if_pos hadj]
      omega
    · have h1 := cn_nonadj i j hij hadj
      have h2 := sq_cn i j
      rw [h1] at h2
      have h3 : A i j = 0 := by simp only [hA]; rw [if_neg hadj]
      omega

/-- Forward direction: the adjacency matrix yields a Conway 99 line system. -/
lemma fwd_dir (A : Matrix (Fin 99) (Fin 99) ℕ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hsymm : ∀ i j, A i j = A j i)
    (hdiag : ∀ i, A i i = 0)
    (hmat : ∀ i j, (∑ k, A i k * A k j) + A i j = (if i = j then 12 else 0) + 2) :
    ∃ L : Finset (Finset (Fin 99)),
      (∀ l ∈ L, l.card = 3) ∧
      (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1) ∧
      (∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7) ∧
      (∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (Finset.univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2) := by
  classical
  -- Lines are the triangles of the graph.
  set L : Finset (Finset (Fin 99)) :=
    (Finset.univ.powersetCard 3).filter
      fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → A x y = 1 with hL
  have memL : ∀ s : Finset (Fin 99), s ∈ L ↔
      (s ∈ Finset.univ.powersetCard 3 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → A x y = 1) := by
    intro s
    rw [hL]
    exact Finset.mem_filter
  have cardL : ∀ l ∈ L, l.card = 3 := by
    intro l hl
    rw [memL, Finset.mem_powersetCard] at hl
    exact hl.1.2
  have adj_symm : ∀ i j : Fin 99, A i j = 1 → A j i = 1 := by
    intro i j h
    exact (hsymm i j).symm.trans h
  have adj_irrefl : ∀ i : Fin 99, A i i ≠ 1 := by
    intro i h
    rw [hdiag i] at h
    exact zero_ne_one h
  -- Every vertex has 14 neighbours.
  have deg14 : ∀ i : Fin 99, (Finset.univ.filter fun k => A i k = 1).card = 14 := by
    intro i
    have hsq : ∀ k : Fin 99, A i k * A k i = A i k := by
      intro k
      have e : A k i = A i k := (hsymm i k).symm
      rw [e]
      rcases h01 i k with h | h <;> rw [h] <;> norm_num
    have hme := hmat i i
    rw [hdiag i, if_pos rfl, Finset.sum_congr rfl (fun k _ => hsq k), add_zero] at hme
    have hsum : ∑ k : Fin 99, A i k = 14 := by omega
    have hterm : ∀ k : Fin 99, A i k = (if A i k = 1 then (1 : ℕ) else 0) := by
      intro k
      rcases h01 i k with h | h <;> simp [h]
    have hcard : (Finset.univ.filter fun k => A i k = 1).card
        = ∑ k : Fin 99, (if A i k = 1 then (1 : ℕ) else 0) := by
      rw [Finset.sum_boole, Nat.cast_id]
    calc (Finset.univ.filter fun k => A i k = 1).card
        = ∑ k : Fin 99, (if A i k = 1 then (1 : ℕ) else 0) := hcard
      _ = ∑ k : Fin 99, A i k := Finset.sum_congr rfl (fun k _ => (hterm k).symm)
      _ = 14 := hsum
  -- Common-neighbour counts as a matrix square.
  have cn_card : ∀ i j : Fin 99,
      (Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1).card = ∑ k : Fin 99, A i k * A k j := by
    intro i j
    have hterm : ∀ k : Fin 99, A i k * A k j
        = (if A i k = 1 ∧ A k j = 1 then (1 : ℕ) else 0) := by
      intro k
      rcases h01 i k with h1 | h1 <;> rcases h01 k j with h2 | h2 <;> simp [h1, h2]
    calc (Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1).card
        = ∑ k : Fin 99, (if A i k = 1 ∧ A k j = 1 then (1 : ℕ) else 0) := by
          rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ k : Fin 99, A i k * A k j :=
          (Finset.sum_congr rfl (fun k _ => (hterm k).symm))
  -- Adjacent vertices have exactly one common neighbour (λ = 1).
  have lam1 : ∀ i j : Fin 99, i ≠ j → A i j = 1 →
      (Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1).card = 1 := by
    intro i j hne hadj
    rw [cn_card i j]
    have hme := hmat i j
    rw [if_neg hne, hadj] at hme
    omega
  -- Non-adjacent vertices have exactly two common neighbours (μ = 2).
  have mu2 : ∀ i j : Fin 99, i ≠ j → A i j ≠ 1 →
      (Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1).card = 2 := by
    intro i j hne hnadj
    have h0 : A i j = 0 := by
      rcases h01 i j with h | h
      · exact h
      · exact absurd h hnadj
    rw [cn_card i j]
    have hme := hmat i j
    rw [if_neg hne, h0] at hme
    omega
  -- Every edge lies in a unique triangle.
  have tri_ex : ∀ i j : Fin 99, i ≠ j → A i j = 1 →
      ∃ z : Fin 99, z ≠ i ∧ z ≠ j ∧ A i z = 1 ∧ A z j = 1 ∧
        (∀ w : Fin 99, A i w = 1 → A w j = 1 → w = z) := by
    intro i j hne hadj
    have h1 : (Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1).card = 1 := lam1 i j hne hadj
    rw [Finset.card_eq_one] at h1
    obtain ⟨z, hz⟩ := h1
    have hmem : z ∈ Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1 := by
      rw [hz]; exact Finset.mem_singleton_self z
    rw [Finset.mem_filter] at hmem
    obtain ⟨_, hiz, hzj⟩ := hmem
    have hzi : z ≠ i := by
      intro hzi
      rw [hzi] at hiz
      exact adj_irrefl i hiz
    have hzj' : z ≠ j := by
      intro hzj''
      rw [hzj''] at hzj
      exact adj_irrefl j hzj
    refine ⟨z, hzi, hzj', hiz, hzj, ?_⟩
    intro w hiw hwj
    have hmemw : w ∈ Finset.univ.filter fun k => A i k = 1 ∧ A k j = 1 := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ w, hiw, hwj⟩
    rw [hz, Finset.mem_singleton] at hmemw
    exact hmemw
  have tri_card3 : ∀ i j z : Fin 99, i ≠ j → z ≠ i → z ≠ j →
      (({i, j, z} : Finset (Fin 99))).card = 3 := by
    intro i j z hne hzi hzj
    have h1 : i ∉ ({j, z} : Finset (Fin 99)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, Ne.symm hzi⟩
    have h2 : j ∉ ({z} : Finset (Fin 99)) := by
      rw [Finset.mem_singleton]
      exact Ne.symm hzj
    have e1 := Finset.card_insert_of_notMem h1
    have e2 := Finset.card_insert_of_notMem h2
    have e3 := Finset.card_singleton z
    omega
  have tri_mem : ∀ i j z : Fin 99, i ≠ j → A i j = 1 → z ≠ i → z ≠ j →
      A i z = 1 → A z j = 1 → (({i, j, z} : Finset (Fin 99)) ∈ L) := by
    intro i j z hne hadj hzi hzj hiz hzj2
    rw [memL]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      exact tri_card3 i j z hne hzi hzj
    · intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with h1 | h1 | h1 <;> rcases hy with h2 | h2 | h2
      · rw [h1, h2] at hxy; exact absurd rfl hxy
      · rw [h1, h2]; exact hadj
      · rw [h1, h2]; exact hiz
      · rw [h1, h2]; exact adj_symm i j hadj
      · rw [h1, h2] at hxy; exact absurd rfl hxy
      · rw [h1, h2]; exact adj_symm z j hzj2
      · rw [h1, h2]; exact adj_symm i z hiz
      · rw [h1, h2]; exact hzj2
      · rw [h1, h2] at hxy; exact absurd rfl hxy
  have third_point : ∀ l ∈ L, ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∃ z ∈ l, z ≠ x ∧ z ≠ y := by
    intro l hl x hx y hy hxy
    have hlc := cardL l hl
    have e1 : (l.erase x).card = 2 := by
      have her := Finset.card_erase_of_mem hx
      omega
    have hy1 : y ∈ l.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
    have e2 : ((l.erase x).erase y).card = 1 := by
      have her := Finset.card_erase_of_mem hy1
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((l.erase x).erase y).card)
    rw [Finset.mem_erase] at hz
    obtain ⟨hzy, hz⟩ := hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hzx, hz⟩ := hz
    exact ⟨z, hz, hzx, hzy⟩
  -- A line through i, j is determined by the unique third vertex.
  have tri_eq : ∀ i j z : Fin 99, i ≠ j → A i j = 1 → z ≠ i → z ≠ j →
      (∀ w : Fin 99, A i w = 1 → A w j = 1 → w = z) →
      ∀ l ∈ L, i ∈ l → j ∈ l → l = ({i, j, z} : Finset (Fin 99)) := by
    intro i j z hne hadj hzi hzj huniq l hl hil hjl
    obtain ⟨w, hwl, hwi, hwj⟩ := third_point l hl i hil j hjl hne
    have htri : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → A a b = 1 := ((memL l).mp hl).2
    have hwadj1 : A i w = 1 := htri i hil w hwl (Ne.symm hwi)
    have hwadj2 : A w j = 1 := htri w hwl j hjl hwj
    have hwz : w = z := huniq w hwadj1 hwadj2
    have hzi' : w ≠ i := by rw [hwz]; exact hzi
    have hzj' : w ≠ j := by rw [hwz]; exact hzj
    have hc3 := tri_card3 i j w hne hzi' hzj'
    have hlc := cardL l hl
    have hsub : (({i, j, w} : Finset (Fin 99))) ⊆ l := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hil
      · exact hjl
      · exact hwl
    have hle : l.card ≤ (({i, j, w} : Finset (Fin 99))).card := by rw [hlc, hc3]
    have heq : l = (({i, j, w} : Finset (Fin 99))) :=
      (Finset.eq_of_subset_of_card_le hsub hle).symm
    rw [hwz] at heq
    exact heq
  -- Any three distinct collinear points determine the line.
  have line_eq : ∀ l ∈ L, ∀ x ∈ l, ∀ y ∈ l, ∀ z ∈ l, x ≠ y → z ≠ x → z ≠ y →
      l = ({x, y, z} : Finset (Fin 99)) := by
    intro l hl x hx y hy z hz hxy hzx hzy
    have hlc := cardL l hl
    have hc3 := tri_card3 x y z hxy hzx hzy
    have hsub : (({x, y, z} : Finset (Fin 99))) ⊆ l := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    have hle : l.card ≤ (({x, y, z} : Finset (Fin 99))).card := by rw [hlc, hc3]
    exact (Finset.eq_of_subset_of_card_le hsub hle).symm
  -- Seven lines through each vertex: the 14 neighbours pair up via the
  -- unique triangles.
  have seven : ∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7 := by
    intro x
    set Tx : Finset (Finset (Fin 99)) := L.filter fun l => x ∈ l with hTx
    have hNx14 : (Finset.univ.filter fun k => A x k = 1).card = 14 := deg14 x
    have row1 : ∀ y ∈ Finset.univ.filter (fun k => A x k = 1),
        (Tx.filter fun l => y ∈ l).card = 1 := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_, hay⟩ := hy
      have hxy : x ≠ y := by
        intro hxy'
        rw [hxy'] at hay
        exact adj_irrefl y hay
      obtain ⟨z, hzi, hzj, hiz, hzj2, huniq⟩ := tri_ex x y hxy hay
      have heq : Tx.filter (fun l => y ∈ l) = ({{x, y, z}} : Finset (Finset (Fin 99))) := by
        apply Finset.ext; intro l
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hlTx, hyl⟩
          rw [hTx, Finset.mem_filter] at hlTx
          obtain ⟨hlL, hxl⟩ := hlTx
          exact tri_eq x y z hxy hay hzi hzj huniq l hlL hxl hyl
        · intro h
          subst h
          rw [hTx, Finset.mem_filter]
          exact ⟨⟨tri_mem x y z hxy hay hzi hzj hiz hzj2, by simp⟩, by simp⟩
      rw [heq, Finset.card_singleton]
    have col2 : ∀ l ∈ Tx, ((Finset.univ.filter fun k => A x k = 1).filter fun y => y ∈ l).card
        = 2 := by
      intro l hl
      rw [hTx, Finset.mem_filter] at hl
      obtain ⟨hlL, hxl⟩ := hl
      rw [memL] at hlL
      have hlL0 : l ∈ L := (memL l).mpr ⟨hlL.1, hlL.2⟩
      have heq : (Finset.univ.filter fun k => A x k = 1).filter (fun y => y ∈ l)
          = l.erase x := by
        apply Finset.ext; intro y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨hay, hyl⟩
          refine ⟨?_, hyl⟩
          intro hyx
          rw [hyx] at hay
          exact adj_irrefl x hay
        · rintro ⟨hyx, hyl⟩
          exact ⟨hlL.2 x hxl y hyl (Ne.symm hyx), hyl⟩
      rw [heq]
      have hlc := cardL l hlL0
      have her := Finset.card_erase_of_mem hxl
      omega
    have dbl : (∑ y ∈ Finset.univ.filter (fun k => A x k = 1), ∑ l ∈ Tx, (if y ∈ l then (1 : ℕ) else 0))
        = ∑ l ∈ Tx, ∑ y ∈ Finset.univ.filter (fun k => A x k = 1), (if y ∈ l then (1 : ℕ) else 0) :=
      Finset.sum_comm
    have hrow : ∀ y ∈ Finset.univ.filter (fun k => A x k = 1),
        (∑ l ∈ Tx, (if y ∈ l then (1 : ℕ) else 0)) = 1 := by
      intro y hy
      rw [Finset.sum_boole, Nat.cast_id]
      exact row1 y hy
    have hcol : ∀ l ∈ Tx,
        (∑ y ∈ Finset.univ.filter (fun k => A x k = 1), (if y ∈ l then (1 : ℕ) else 0)) = 2 := by
      intro l hl
      rw [Finset.sum_boole, Nat.cast_id]
      exact col2 l hl
    have hLHS : (∑ y ∈ Finset.univ.filter (fun k => A x k = 1),
        ∑ l ∈ Tx, (if y ∈ l then (1 : ℕ) else 0)) = 14 := by
      have h := Finset.sum_congr rfl (fun y hy => hrow y hy)
      rw [h, Finset.sum_const, hNx14, nsmul_eq_mul, mul_one, Nat.cast_id]
    have hRHS : (∑ l ∈ Tx, ∑ y ∈ Finset.univ.filter (fun k => A x k = 1),
        (if y ∈ l then (1 : ℕ) else 0)) = 2 * Tx.card := by
      have h := Finset.sum_congr rfl (fun l hl => hcol l hl)
      rw [h, Finset.sum_const, nsmul_eq_mul, mul_comm, Nat.cast_id]
    rw [hLHS, hRHS] at dbl
    omega
  -- Non-collinear pairs see exactly the two common neighbours.
  have hnc : ∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
      (Finset.univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
          (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2 := by
    intro x y hxy hnl
    have hnadj : A x y ≠ 1 := by
      intro hadj
      obtain ⟨z, hzi, hzj, hiz, hzj2, huniq⟩ := tri_ex x y hxy hadj
      have htri := tri_mem x y z hxy hadj hzi hzj hiz hzj2
      have hmem : x ∈ ({x, y, z} : Finset (Fin 99)) ∧ y ∈ ({x, y, z} : Finset (Fin 99)) :=
        ⟨by simp, by simp⟩
      exact hnl {x, y, z} htri hmem
    have hmu := mu2 x y hxy hnadj
    have heq : Finset.univ.filter
          (fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧ (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l))
        = Finset.univ.filter fun k => A x k = 1 ∧ A k y = 1 := by
      apply Finset.ext; intro z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hzi, hzj, ⟨l₁, hl₁, hx1, hz1⟩, ⟨l₂, hl₂, hy2, hz2⟩⟩
        have h1 := (memL l₁).mp hl₁
        have h2 := (memL l₂).mp hl₂
        exact ⟨h1.2 x hx1 z hz1 (Ne.symm hzi), h2.2 z hz2 y hy2 hzj⟩
      · rintro ⟨hxz, hzy⟩
        have hzx : z ≠ x := by
          intro hcon
          rw [hcon] at hxz
          exact adj_irrefl x hxz
        have hzy' : z ≠ y := by
          intro hcon
          rw [hcon] at hzy
          exact adj_irrefl y hzy
        obtain ⟨w₁, hw₁x, hw₁z, hxw₁, hw₁z', _⟩ := tri_ex x z (Ne.symm hzx) hxz
        obtain ⟨w₂, hw₂z, hw₂y, hzw₂, hw₂y', _⟩ := tri_ex z y hzy' hzy
        refine ⟨hzx, hzy', ?_, ?_⟩
        · exact ⟨{x, z, w₁}, tri_mem x z w₁ (Ne.symm hzx) hxz hw₁x hw₁z hxw₁ hw₁z',
            by simp, by simp⟩
        · exact ⟨{z, y, w₂}, tri_mem z y w₂ hzy' hzy hw₂z hw₂y hzw₂ hw₂y',
            by simp, by simp⟩
    rw [heq]
    exact hmu
  -- Distinct lines meet in at most one point.
  have hinter : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1 := by
    intro l₁ hl₁ l₂ hl₂ hne
    by_contra hlt
    have h2lt : 1 < (l₁ ∩ l₂).card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2lt
    rw [Finset.mem_inter] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hadj : A x y = 1 := ((memL l₁).mp hl₁).2 x hx1 y hy1 hxy
    obtain ⟨z₁, hz₁, hz₁x, hz₁y⟩ := third_point l₁ hl₁ x hx1 y hy1 hxy
    obtain ⟨z₂, hz₂, hz₂x, hz₂y⟩ := third_point l₂ hl₂ x hx2 y hy2 hxy
    have hc1 : A x z₁ = 1 ∧ A z₁ y = 1 := by
      have hlm := (memL l₁).mp hl₁
      exact ⟨hlm.2 x hx1 z₁ hz₁ (Ne.symm hz₁x), hlm.2 z₁ hz₁ y hy1 hz₁y⟩
    have hc2 : A x z₂ = 1 ∧ A z₂ y = 1 := by
      have hlm := (memL l₂).mp hl₂
      exact ⟨hlm.2 x hx2 z₂ hz₂ (Ne.symm hz₂x), hlm.2 z₂ hz₂ y hy2 hz₂y⟩
    have hzne : z₁ ≠ z₂ := by
      intro hzz
      apply hne
      rw [line_eq l₁ hl₁ x hx1 y hy1 z₁ hz₁ hxy hz₁x hz₁y,
        line_eq l₂ hl₂ x hx2 y hy2 z₂ hz₂ hxy hz₂x hz₂y, hzz]
    have hlam := lam1 x y hxy hadj
    have hsub : ({z₁, z₂} : Finset (Fin 99)) ⊆
        Finset.univ.filter fun k => A x k = 1 ∧ A k y = 1 := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ w, ?_⟩
      rcases hw with rfl | rfl
      · exact hc1
      · exact hc2
    have hle := Finset.card_le_card hsub
    rw [hlam] at hle
    have hc2card : ({z₁, z₂} : Finset (Fin 99)).card = 2 := by
      have h1 : z₁ ∉ ({z₂} : Finset (Fin 99)) := by
        rw [Finset.mem_singleton]; exact hzne
      have e1 := Finset.card_insert_of_notMem h1
      have e2 := Finset.card_singleton z₂
      omega
    omega
  refine ⟨L, cardL, hinter, seven, hnc⟩

theorem solution :
    (∃ L : Finset (Finset (Fin 99)),
      (∀ l ∈ L, l.card = 3) ∧
      (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1) ∧
      (∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7) ∧
      (∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (Finset.univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2))
    ↔
    (∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j = (if i = j then 12 else 0) + 2)) := by
  constructor
  · intro h
    obtain ⟨L, h3, hInt, h7, hμ⟩ := h
    exact back_dir L h3 hInt h7 hμ
  · intro h
    obtain ⟨A, h01, hsymm, hdiag, hmat⟩ := h
    exact fwd_dir A h01 hsymm hdiag hmat
