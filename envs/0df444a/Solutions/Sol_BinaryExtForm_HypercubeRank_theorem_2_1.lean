-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:07:52.131287+00:00
-- url     : https://prove2.me/submissions/29df7505-5c3d-4299-89cd-2f37a4fdf6d7

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

set_option autoImplicit false

open Disjunctive.HigherDim

namespace BinaryExtForm.HypercubeRank.BalasProof

lemma convexHull_binary_subset {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n)
    (hbox : ∀ x ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    convexHull ℝ S ∩ ZeroOneSet i ⊆ convexHull ℝ (S ∩ ZeroOneSet i) := by
  let C := convexHull ℝ (S ∩ ZeroOneSet i)
  let T : Set (Fin n → ℝ) := {x | 0 ≤ x i ∧ x i ≤ 1 ∧
    (x i = 0 ∨ x i = 1 → x ∈ C)}
  have hST : S ⊆ T := by
    intro x hx
    exact ⟨(hbox x hx).1, (hbox x hx).2,
      fun hb => subset_convexHull ℝ (S ∩ ZeroOneSet i) ⟨hx,hb⟩⟩
  have hT : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0,hb1] using hy
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0,ha1] using hx
    change 0 ≤ x i ∧ x i ≤ 1 ∧ (x i = 0 ∨ x i = 1 → x ∈ C) at hx
    change 0 ≤ y i ∧ y i ≤ 1 ∧ (y i = 0 ∨ y i = 1 → y ∈ C) at hy
    change 0 ≤ a*x i+b*y i ∧ a*x i+b*y i ≤ 1 ∧
      (a*x i+b*y i = 0 ∨ a*x i+b*y i = 1 → a • x+b • y ∈ C)
    have hlow : 0 ≤ a*x i+b*y i := add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    have hupp : a*x i+b*y i ≤ 1 := by
      have hax := mul_le_mul_of_nonneg_left hx.2.1 ha
      have hby := mul_le_mul_of_nonneg_left hy.2.1 hb
      nlinarith
    refine ⟨hlow,hupp,?_⟩
    intro he
    rcases he with he | he
    · have hz := (add_eq_zero_iff_of_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)).mp he
      have hxi : x i = 0 := (mul_eq_zero.mp hz.1).resolve_left ha0
      have hyi : y i = 0 := (mul_eq_zero.mp hz.2).resolve_left hb0
      exact (convex_convexHull ℝ (S ∩ ZeroOneSet i))
        (hx.2.2 (Or.inl hxi)) (hy.2.2 (Or.inl hyi)) ha hb hab
    · have hdef : a*(1-x i)+b*(1-y i) = 0 := by nlinarith
      have hz := (add_eq_zero_iff_of_nonneg (mul_nonneg ha (sub_nonneg.mpr hx.2.1))
        (mul_nonneg hb (sub_nonneg.mpr hy.2.1))).mp hdef
      have hxi : x i = 1 := by have := (mul_eq_zero.mp hz.1).resolve_left ha0; linarith
      have hyi : y i = 1 := by have := (mul_eq_zero.mp hz.2).resolve_left hb0; linarith
      exact (convex_convexHull ℝ (S ∩ ZeroOneSet i))
        (hx.2.2 (Or.inr hxi)) (hy.2.2 (Or.inr hyi)) ha hb hab
  intro x hx
  exact (convexHull_min hST hT hx.1).2.2 hx.2

lemma split_convexHull_eq {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n)
    (hbox : ∀ x ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    SplitConvexify (convexHull ℝ S) i = convexHull ℝ (S ∩ ZeroOneSet i) := by
  unfold SplitConvexify
  apply Set.Subset.antisymm
  · exact convexHull_min (convexHull_binary_subset S i hbox) (convex_convexHull ℝ _)
  · exact convexHull_mono (fun x hx => ⟨subset_convexHull ℝ S hx.1, hx.2⟩)

lemma iteratedSplit_convexHull {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1) :
    IteratedSplit (convexHull ℝ S) l =
      convexHull ℝ (S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}) := by
  induction l generalizing S with
  | nil => simp [IteratedSplit]
  | cons i l ih =>
    change IteratedSplit (SplitConvexify (convexHull ℝ S) i) l = _
    rw [split_convexHull_eq S i (fun x hx => hbox x hx i (by simp))]
    rw [ih (S ∩ ZeroOneSet i) (fun x hx k hk => hbox x hx.1 k (by simp [hk]))]
    congr 1
    ext x
    simp [List.mem_cons, and_assoc]

lemma convexHull_binary_restriction {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ convexHull ℝ S) (hbin : ∀ i ∈ l, x ∈ ZeroOneSet i) :
    x ∈ convexHull ℝ (S ∩ {z | ∀ i ∈ l, z ∈ ZeroOneSet i}) := by
  induction l generalizing S with
  | nil => simpa using hx
  | cons i l ih =>
    have hx' : x ∈ convexHull ℝ (S ∩ ZeroOneSet i) :=
      convexHull_binary_subset S i (fun z hz => hbox z hz i (by simp))
        ⟨hx,hbin i (by simp)⟩
    have hr := ih (S ∩ ZeroOneSet i) (fun z hz k hk => hbox z hz.1 k (by simp [hk]))
      hx' (fun k hk => hbin k (by simp [hk]))
    have heq : (S ∩ ZeroOneSet i) ∩ {z | ∀ k ∈ l, z ∈ ZeroOneSet k} =
        S ∩ {z | ∀ k ∈ i::l, z ∈ ZeroOneSet k} := by
      ext z
      simp [List.mem_cons,and_assoc]
    rwa [heq] at hr

lemma binary_restriction_nonempty_iff {n : ℕ} (S : Set (Fin n → ℝ)) (l : List (Fin n))
    (hbox : ∀ x ∈ S, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1) :
    (convexHull ℝ S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}).Nonempty ↔
      (S ∩ {x | ∀ i ∈ l, x ∈ ZeroOneSet i}).Nonempty := by
  constructor
  · rintro ⟨x,hx,hbin⟩
    exact convexHull_nonempty_iff.mp ⟨x,convexHull_binary_restriction S l hbox hx hbin⟩
  · rintro ⟨x,hx,hbin⟩
    exact ⟨x,subset_convexHull ℝ S hx,hbin⟩

lemma binary_restriction_finset_nonempty_iff {n : ℕ} (S : Set (Fin n → ℝ))
    (H : Finset (Fin n)) (hbox : ∀ x ∈ S, ∀ i ∈ H, 0 ≤ x i ∧ x i ≤ 1) :
    (convexHull ℝ S ∩ ⋂ i ∈ H, ZeroOneSet i).Nonempty ↔
      (S ∩ ⋂ i ∈ H, ZeroOneSet i).Nonempty := by
  classical
  have heq : {x : Fin n → ℝ | ∀ i ∈ H.toList, x ∈ ZeroOneSet i} =
      ⋂ i ∈ H, ZeroOneSet i := by
    ext x
    simp
  rw [← heq]
  exact binary_restriction_nonempty_iff S H.toList (by simpa using hbox)

end BinaryExtForm.HypercubeRank.BalasProof

open BinaryExtForm.HypercubeRank

theorem solution {n : ℕ} (Q : Set (Fin n → ℝ)) (H : Finset (Fin n)) (hQ : IsPolytope Q)
    (hQH : ∀ p ∈ Q, ∀ i ∈ H, 0 ≤ p i ∧ p i ≤ 1) (l : List (Fin n)) (hl : l.Nodup)
    (hlH : l.toFinset = H) :
    IteratedSplit Q l = intHull Q H := by
  have _hl := hl
  have hconv : Convex ℝ Q := by
    obtain ⟨S,rfl⟩ := hQ
    exact convex_convexHull ℝ _
  have hbox : ∀ x ∈ Q, ∀ i ∈ l, 0 ≤ x i ∧ x i ≤ 1 := by
    intro x hx i hi
    apply hQH x hx i
    rw [← hlH]
    exact List.mem_toFinset.mpr hi
  have h := BalasProof.iteratedSplit_convexHull Q l hbox
  rw [hconv.convexHull_eq] at h
  rw [h]
  unfold intHull
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [← hlH]
  simp only [List.mem_toFinset]
