-- Prove2me | solution 1 for DistInterpRO.Equivalence.nested_dual_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:02:57.309042+00:00
-- url     : https://prove2.me/submissions/3771d674-cb84-4e78-a9b0-2ac6d61d9b8f

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory


namespace DistInterpRO.Equivalence

noncomputable def gext {n : ℕ} (fi : Fin n → ℝ) (t : ℕ) : ℝ :=
  if h : t < n then fi ⟨t, h⟩ else 0

lemma nestedDual_eq {n : ℕ} (fi : Fin n → ℝ) (S : Finset (Fin n)) :
    nestedDual fi S = ∑ i : Fin n,
      if S = Finset.Iic i then gext fi i.val - gext fi (i.val + 1) else 0 := by
  unfold nestedDual gext
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]

lemma nestedDual_swap {n : ℕ} (fi : Fin n → ℝ) (w : Finset (Fin n) → ℝ) :
    ∑ S : Finset (Fin n), nestedDual fi S * w S =
      ∑ i : Fin n, (gext fi i.val - gext fi (i.val + 1)) * w (Finset.Iic i) := by
  simp_rw [nestedDual_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

lemma tele_nat (g : ℕ → ℝ) (k : ℕ) : ∀ N, k ≤ N →
    ∑ t ∈ Finset.range N, (g t - g (t + 1)) * (if k ≤ t then (1:ℝ) else 0) = g k - g N := by
  intro N hN
  induction N with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge N k with h | h
    · have hk : k = N + 1 := by omega
      subst hk
      have : ∀ t ∈ Finset.range N, (g t - g (t + 1)) * (if N + 1 ≤ t then (1:ℝ) else 0) = 0 := by
        intro t ht
        simp at ht
        have : ¬ (N + 1 ≤ t) := by omega
        simp [this]
      rw [Finset.sum_eq_zero this]
      simp
    · rw [ih h]
      simp [h]

lemma tele_fin {n : ℕ} (fi : Fin n → ℝ) (k : Fin n) :
    ∑ i : Fin n, (gext fi i.val - gext fi (i.val + 1)) * (if k ≤ i then (1:ℝ) else 0) = fi k := by
  have := tele_nat (gext fi) k.val n k.isLt.le
  rw [Finset.sum_range (fun t => (gext fi t - gext fi (t + 1)) *
    (if k.val ≤ t then (1:ℝ) else 0))] at this
  simp only [Fin.le_iff_val_le_val]
  rw [this]
  simp [gext, k.isLt]

theorem nested_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ)
    (Z : Fin n → Set (Fin m → ℝ))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (hsorted : Antitone (fun i : Fin n => ⨅ x : Z i, f x)) :
    IsDualFeasible Z f (nestedDual (fun i => ⨅ x : Z i, f x)) ∧
      (∀ i : Fin n, ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
            ⨅ x : Z i, f x) ∧
      ∑ i, c i * ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
        ∑ i, c i * ⨅ x : Z i, f x := by
  classical
  set fi : Fin n → ℝ := fun i => ⨅ x : Z i, f x with hfi
  have P2 : ∀ i : Fin n, ∑ S : Finset (Fin n),
      nestedDual fi S * (if i ∈ S then (1 : ℝ) else 0) = fi i := by
    intro i
    rw [nestedDual_swap]
    simp only [Finset.mem_Iic]
    exact tele_fin fi i
  refine ⟨⟨?_, ?_⟩, P2, ?_⟩
  · intro x hx
    have hne : (Finset.univ.filter (fun j => x ∈ Z j)).Nonempty := by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact ⟨j, by simp [hj]⟩
    set k := (Finset.univ.filter (fun j => x ∈ Z j)).min' hne with hk
    have hkmem : x ∈ Z k := by
      have := Finset.min'_mem _ hne
      rw [← hk] at this
      simpa using this
    have hiff : ∀ j : Fin n, (x ∈ ⋃ l ∈ Finset.Iic j, Z l) ↔ k ≤ j := by
      intro j
      simp only [Set.mem_iUnion, Finset.mem_Iic, exists_prop]
      constructor
      · rintro ⟨l, hl, hxl⟩
        have : k ≤ l := Finset.min'_le _ _ (by simp [hxl])
        exact le_trans this hl
      · intro h; exact ⟨k, h, hkmem⟩
    rw [nestedDual_swap]
    simp only [hiff]
    rw [tele_fin fi k]
    have hb : BddBelow (Set.range fun y : Z k => f y) := by
      rw [← Set.image_eq_range]; exact hbdd k
    exact ciInf_le hb ⟨x, hkmem⟩
  · intro S hS
    rw [nestedDual_eq]
    apply Finset.sum_nonneg
    intro i _
    split_ifs with h
    · by_cases hi : i.val + 1 < n
      · have e1 : gext fi i.val = fi i := by simp [gext, i.isLt]
        have e2 : gext fi (i.val + 1) = fi ⟨i.val + 1, hi⟩ := by simp [gext, hi]
        rw [e1, e2, sub_nonneg]
        apply hsorted
        rw [Fin.le_iff_val_le_val]; simp
      · exfalso; apply hS
        rw [h]
        ext j
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
        rw [Fin.le_iff_val_le_val]; omega
    · exact le_rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [P2 i]

end DistInterpRO.Equivalence

open DistInterpRO.Equivalence


theorem solution {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (hsorted : Antitone (fun i : Fin n => ⨅ x : Z i, f x)) :
    IsDualFeasible Z f (nestedDual (fun i => ⨅ x : Z i, f x)) ∧
      (∀ i : Fin n, ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
            ⨅ x : Z i, f x) ∧
      ∑ i, c i * ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
        ∑ i, c i * ⨅ x : Z i, f x := by
  exact nested_core f c Z hbdd hsorted
