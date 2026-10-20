-- Prove2me | solution 1 for EssentialCodingTheory.card_hammingBall
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:58:26.20815+00:00
-- url     : https://prove2.me/submissions/0926ab5b-0927-4614-9152-c9e3cb27d14f

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Finset
noncomputable section

private def mismatchSet {α : Type*} [DecidableEq α] {n : ℕ}
    (x y : Fin n → α) : Finset (Fin n) := univ.filter fun i => x i ≠ y i

private def mismatchFiber {α : Type*} [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (s : Finset (Fin n)) := {y : Fin n → α // mismatchSet x y = s}

private noncomputable instance mismatchFiberFintype {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (x : Fin n → α) (s : Finset (Fin n)) : Fintype (mismatchFiber x s) := by
  classical
  letI : Finite (Fin n → α) := Finite.of_fintype _
  letI : Finite (mismatchFiber x s) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private def mismatchFiberEquiv {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (s : Finset (Fin n)) :
    mismatchFiber x s ≃ ((i : {i : Fin n // i ∈ s}) → {a : α // a ≠ x i}) := by
  classical
  refine {
    toFun := fun y i => ⟨y.1 i.1, ?_⟩
    invFun := fun f => ⟨(fun i => if hi : i ∈ s then f ⟨i, hi⟩ else x i), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have hi : i.1 ∈ mismatchSet x y.1 := by rw [y.2]; exact i.2
    simpa [mismatchSet, ne_comm] using (Finset.mem_filter.mp hi).2
  · apply Finset.ext
    intro i
    by_cases hi : i ∈ s
    · simp [mismatchSet, hi]
      exact (by simpa [ne_comm] using (f ⟨i, hi⟩).property)
    · simp [mismatchSet, hi]
  · intro y
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [hi]
    · have hy : i ∉ mismatchSet x y.1 := by rw [y.2]; exact hi
      have hxy : ¬ x i ≠ y.1 i := by
        intro h
        exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [hi, not_ne_iff.mp hxy]
  · intro f
    funext i
    apply Subtype.ext
    simp [i.property]

private theorem card_ne {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 := by
  classical
  let e : {b : α // b ≠ a} ≃ ({a}ᶜ : Set α) := {
    toFun := fun b => ⟨b.1, by simpa [ne_comm] using b.2⟩
    invFun := fun b => ⟨b.1, by
      intro h
      apply b.2
      simpa using h⟩
    left_inv := by intro b; cases b; rfl
    right_inv := by intro b; cases b; rfl }
  calc
    Fintype.card {b : α // b ≠ a} = Fintype.card (↑({a}ᶜ : Set α)) := Fintype.card_congr e
    _ = Fintype.card α - 1 := by rw [Fintype.card_compl_set]; simp

private theorem mismatchFiber_card {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (s : Finset (Fin n)) [Fintype (mismatchFiber x s)] :
    Fintype.card (mismatchFiber x s) = (Fintype.card α - 1) ^ s.card := by
  classical
  rw [Fintype.card_congr (mismatchFiberEquiv x s)]
  rw [Fintype.card_pi]
  simp_rw [card_ne]
  simp

private noncomputable def ballEquiv {α : Type*} [Fintype α] [DecidableEq α] {n e : ℕ}
    (x : Fin n → α) :
    {y : Fin n → α // hammingDist x y ≤ e} ≃
      Sigma fun s : {s : Finset (Fin n) // s.card ≤ e} => mismatchFiber x s.1 := by
  classical
  refine {
    toFun := fun y => ⟨⟨mismatchSet x y.1, by
      have hy : hammingDist x y.1 = (mismatchSet x y.1).card := by rfl
      rw [← hy]
      exact y.2⟩, ⟨y.1, rfl⟩⟩
    invFun := fun z => ⟨z.2.1, by
      have hy : hammingDist x z.2.1 = z.1.1.card := by
        have h := congrArg Finset.card z.2.2
        simpa [hammingDist, mismatchSet] using h
      rw [hy]
      exact z.1.2⟩
    left_inv := by intro y; apply Subtype.ext; rfl
    right_inv := by
      intro ⟨⟨s, hs⟩, ⟨y, hy⟩⟩
      apply Sigma.ext
      · apply Subtype.ext
        exact hy
      · cases hy
        rfl }

private theorem sum_choose_power {n e k : ℕ} :
    (∑ i ∈ range (n + 1), if i ≤ e then n.choose i * k ^ i else 0) =
      ∑ i ∈ range (e + 1), n.choose i * k ^ i := by
  classical
  by_cases he : e ≤ n
  · rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  · have hne : n < e := Nat.lt_of_not_ge he
    have hleft : (∑ i ∈ range (n + 1), if i ≤ e then n.choose i * k ^ i else 0) =
        ∑ i ∈ range (n + 1), n.choose i * k ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ e := by simp only [mem_range] at hi; omega
      simp [hi']
    rw [hleft]
    apply Finset.sum_subset (s₁ := range (n + 1)) (s₂ := range (e + 1)) ?_ ?_
    · intro i hi
      simp only [mem_range] at hi ⊢
      omega
    · intro i hi hni
      simp only [mem_range] at hi hni
      have h : n < i := by omega
      simp [Nat.choose_eq_zero_of_lt h]

theorem solution {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (e : ℕ) :
    (univ.filter fun y : Fin n → α => hammingDist x y ≤ e).card =
      ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i := by
  classical
  let k : ℕ := Fintype.card α - 1
  calc
    (univ.filter fun y : Fin n → α => hammingDist x y ≤ e).card =
        Fintype.card {y : Fin n → α // hammingDist x y ≤ e} := by
      exact (Fintype.card_subtype (fun y : Fin n → α => hammingDist x y ≤ e)).symm
    _ = Fintype.card (Sigma fun s : {s : Finset (Fin n) // s.card ≤ e} =>
        mismatchFiber x s.1) := Fintype.card_congr (ballEquiv x)
    _ = ∑ s : {s : Finset (Fin n) // s.card ≤ e},
        Fintype.card (mismatchFiber x s.1) := Fintype.card_sigma
    _ = ∑ s : {s : Finset (Fin n) // s.card ≤ e}, k ^ s.1.card := by
      simp_rw [mismatchFiber_card, k]
    _ = ∑ s ∈ univ.filter (fun s : Finset (Fin n) => s.card ≤ e), k ^ s.card := by
      symm
      exact Finset.sum_subtype (s := univ.filter (fun s : Finset (Fin n) => s.card ≤ e))
        (h := by simp) (f := fun s : Finset (Fin n) => k ^ s.card)
    _ = ∑ s ∈ (univ : Finset (Finset (Fin n))),
        if s.card ≤ e then k ^ s.card else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ range (n + 1),
        if i ≤ e then n.choose i * k ^ i else 0 := by
      rw [← Finset.powerset_univ, Finset.powerset_card_disjiUnion]
      rw [Finset.sum_disjiUnion (h :=
        (Finset.pairwise_disjoint_powersetCard (univ : Finset (Fin n))).set_pairwise _)]
      have hcard : (univ : Finset (Fin n)).card = n := by simp
      rw [hcard]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hie : i ≤ e
      · simp only [if_pos hie]
        have hconst : ∑ s ∈ powersetCard i (univ : Finset (Fin n)), k ^ s.card =
            (powersetCard i (univ : Finset (Fin n))).card * k ^ i := by
          calc
            _ = ∑ s ∈ powersetCard i (univ : Finset (Fin n)), k ^ i := by
              apply Finset.sum_congr rfl
              intro s hs
              simp [mem_powersetCard.mp hs]
            _ = _ := by
              apply Finset.sum_const_nat
              intro s hs
              rfl
        calc
          (∑ s ∈ powersetCard i (univ : Finset (Fin n)),
              if s.card ≤ e then k ^ s.card else 0) =
              ∑ s ∈ powersetCard i (univ : Finset (Fin n)), k ^ s.card := by
                apply Finset.sum_congr rfl
                intro s hs
                have hsi := (mem_powersetCard.mp hs).2
                simp [hsi, hie]
          _ = (powersetCard i (univ : Finset (Fin n))).card * k ^ i := hconst
          _ = n.choose i * k ^ i := by
            rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      · simp only [if_neg hie]
        apply Finset.sum_eq_zero
        intro s hs
        simp only [mem_powersetCard] at hs
        simp [hs.2, hie]
    _ = ∑ i ∈ range (e + 1), n.choose i * k ^ i := sum_choose_power
    _ = ∑ i ∈ range (e + 1), n.choose i * (Fintype.card α - 1) ^ i := by rfl
