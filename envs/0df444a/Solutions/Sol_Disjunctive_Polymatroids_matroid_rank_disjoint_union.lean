-- Prove2me | solution 1 for Disjunctive.Polymatroids.matroid_rank_disjoint_union
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:31:49.509161+00:00
-- url     : https://prove2.me/submissions/41973f87-36e1-4fa0-843e-dcc2183ab208

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic



namespace Disjunctive.Polymatroids

lemma mr_sum_le_card {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (A : Finset (Fin k)) : SumOver x A ≤ A.card := by
  unfold SumOver
  calc ∑ j ∈ A, x j ≤ ∑ _j ∈ A, (1:ℝ) := Finset.sum_le_sum (fun j _ => (hx j).2)
    _ = A.card := by simp

lemma mr_sum_nonneg {k : ℕ} (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (A : Finset (Fin k)) : 0 ≤ SumOver x A :=
  Finset.sum_nonneg (fun j _ => (hx j).1)

lemma mr_side {k : ℕ} (r : Finset (Fin k) → ℝ) (hmono : ∀ A B : Finset (Fin k), A ⊆ B → r A ≤ r B)
    (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hK : ∀ A : Finset (Fin k), r A < A.card → a * ((A.card : ℝ) - r A) ≤ A.card - SumOver x A) :
    (fun i => max 0 (1 - (1 - x i) / a)) ∈ PolymatroidP r ∧
      (∀ i, 0 ≤ max 0 (1 - (1 - x i) / a) ∧ max 0 (1 - (1 - x i) / a) ≤ 1) ∧
      (∀ i, 0 ≤ (x i - a * max 0 (1 - (1 - x i) / a)) / (1 - a) ∧
        (x i - a * max 0 (1 - (1 - x i) / a)) / (1 - a) ≤ 1) := by
  have hb : 0 < 1 - a := by linarith
  refine ⟨⟨fun i => le_max_left _ _, ?_⟩, ?_, ?_⟩
  · intro A
    set A' := A.filter (fun i => 1 - x i ≤ a) with hA'
    have hsum : SumOver (fun i => max 0 (1 - (1 - x i) / a)) A =
        (A'.card : ℝ) - (A'.card - SumOver x A') / a := by
      unfold SumOver
      have h1 : ∑ j ∈ A, max 0 (1 - (1 - x j) / a) =
          ∑ j ∈ A, (if 1 - x j ≤ a then (1 - (1 - x j) / a) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with h
        · apply max_eq_right
          rw [sub_nonneg, div_le_one ha0]; exact h
        · apply max_eq_left
          rw [sub_nonpos, le_div_iff₀ ha0]; linarith
      rw [h1, ← Finset.sum_filter, ← hA', Finset.sum_sub_distrib, ← Finset.sum_div,
        Finset.sum_sub_distrib]
      simp
    rw [hsum]
    have hsub : A' ⊆ A := Finset.filter_subset _ _
    have hm := hmono A' A hsub
    have hs0 : 0 ≤ (A'.card : ℝ) - SumOver x A' := by
      have := mr_sum_le_card x hx A'; linarith
    rcases lt_or_ge (r A') (A'.card) with h | h
    · have := hK A' h
      have : (A'.card : ℝ) - r A' ≤ ((A'.card : ℝ) - SumOver x A') / a := by
        rw [le_div_iff₀ ha0]; linarith
      linarith
    · have : 0 ≤ ((A'.card : ℝ) - SumOver x A') / a := div_nonneg hs0 ha0.le
      linarith
  · intro i
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    have : 0 ≤ (1 - x i) / a := div_nonneg (by linarith [(hx i).2]) ha0.le
    linarith
  · intro i
    rcases le_total (1 - (1 - x i) / a) 0 with h | h
    · rw [max_eq_left h]
      have : x i ≤ 1 - a := by
        rw [sub_nonpos, le_div_iff₀ ha0] at h; linarith
      constructor
      · exact div_nonneg (by linarith [(hx i).1]) hb.le
      · rw [div_le_one hb]; linarith
    · rw [max_eq_right h]
      have : x i - a * (1 - (1 - x i) / a) = 1 - a := by field_simp; ring
      rw [this, div_self hb.ne']
      exact ⟨zero_le_one, le_rfl⟩

theorem mr_core {m n : ℕ} (r1 : Finset (Fin m) → ℝ)
    (r2 : Finset (Fin n) → ℝ) (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ (ZDisjoint r1 r2) =
      {p : (Fin m → ℝ) × (Fin n → ℝ) | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 1) ∧
        (∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1) ∧
        ∀ A : Finset (Fin m), ∀ B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
          1 ≤ ((A.card : ℝ) - SumOver p.1 A) / ((A.card : ℝ) - r1 A) +
            ((B.card : ℝ) - SumOver p.2 B) / ((B.card : ℝ) - r2 B)} := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
      refine ⟨hx, hy, ?_⟩
      intro A B hA hB
      have dA : 0 < (A.card : ℝ) - r1 A := by linarith
      have dB : 0 < (B.card : ℝ) - r2 B := by linarith
      rcases hxy with h | h
      · have h1 : 1 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) := by
          rw [le_div_iff₀ dA]; linarith [h.2 A]
        have h2 : 0 ≤ ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B) :=
          div_nonneg (by linarith [mr_sum_le_card y hy B]) dB.le
        simpa using add_le_add h1 h2
      · have h1 : 1 ≤ ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B) := by
          rw [le_div_iff₀ dB]; linarith [h.2 B]
        have h2 : 0 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) :=
          div_nonneg (by linarith [mr_sum_le_card x hx A]) dA.le
        simpa using add_le_add h2 h1
    · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩ ⟨x', y'⟩ ⟨hx', hy', hxy'⟩ a b ha hb hab
      simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_setOf_eq, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      refine ⟨fun i => ⟨by nlinarith [hx i, hx' i], by nlinarith [hx i, hx' i]⟩,
        fun j => ⟨by nlinarith [hy j, hy' j], by nlinarith [hy j, hy' j]⟩, ?_⟩
      intro A B hA hB
      have dA : 0 < (A.card : ℝ) - r1 A := by linarith
      have dB : 0 < (B.card : ℝ) - r2 B := by linarith
      have e1 : SumOver (a • x + b • x') A = a * SumOver x A + b * SumOver x' A := by
        simp [SumOver, Finset.sum_add_distrib, Finset.mul_sum]
      have e2 : SumOver (a • y + b • y') B = a * SumOver y B + b * SumOver y' B := by
        simp [SumOver, Finset.sum_add_distrib, Finset.mul_sum]
      rw [e1, e2]
      have h1 := hxy A B hA hB
      have h2 := hxy' A B hA hB
      have key : ((A.card : ℝ) - (a * SumOver x A + b * SumOver x' A)) / ((A.card : ℝ) - r1 A) +
          ((B.card : ℝ) - (a * SumOver y B + b * SumOver y' B)) / ((B.card : ℝ) - r2 B) =
          a * (((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) +
            ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B)) +
          b * (((A.card : ℝ) - SumOver x' A) / ((A.card : ℝ) - r1 A) +
            ((B.card : ℝ) - SumOver y' B) / ((B.card : ℝ) - r2 B)) := by
        have hb' : b = 1 - a := by linarith
        subst hb'
        field_simp
        ring
      rw [key]; nlinarith
  · rintro ⟨x, y⟩ ⟨hx, hy, hineq⟩
    by_cases h1 : x ∈ PolymatroidP r1
    · exact subset_convexHull ℝ _ ⟨hx, hy, Or.inl h1⟩
    by_cases h2 : y ∈ PolymatroidP r2
    · exact subset_convexHull ℝ _ ⟨hx, hy, Or.inr h2⟩
    have hx0 : 0 ≤ x := fun i => (hx i).1
    have hy0 : 0 ≤ y := fun i => (hy i).1
    obtain ⟨A0, hA0⟩ : ∃ A0, r1 A0 < SumOver x A0 := by
      by_contra hc; push_neg at hc; exact h1 ⟨hx0, hc⟩
    obtain ⟨B0, hB0⟩ : ∃ B0, r2 B0 < SumOver y B0 := by
      by_contra hc; push_neg at hc; exact h2 ⟨hy0, hc⟩
    have hA0c : r1 A0 < A0.card := lt_of_lt_of_le hA0 (mr_sum_le_card x hx A0)
    have hB0c : r2 B0 < B0.card := lt_of_lt_of_le hB0 (mr_sum_le_card y hy B0)
    obtain ⟨As, hAs, hmin⟩ := (Finset.univ.filter (fun A : Finset (Fin m) => r1 A < A.card)).exists_min_image
      (fun A => ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A))
      ⟨A0, by simp [hA0c]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hAs hmin
    set a := ((As.card : ℝ) - SumOver x As) / ((As.card : ℝ) - r1 As) with ha_def
    have hK1 : ∀ A : Finset (Fin m), r1 A < A.card →
        a * ((A.card : ℝ) - r1 A) ≤ A.card - SumOver x A := by
      intro A hA
      have := hmin A hA
      rwa [le_div_iff₀ (by linarith)] at this
    have hK2 : ∀ B : Finset (Fin n), r2 B < B.card →
        (1 - a) * ((B.card : ℝ) - r2 B) ≤ B.card - SumOver y B := by
      intro B hB
      have := hineq As B hAs hB
      have : 1 - a ≤ ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B) := by linarith
      rwa [le_div_iff₀ (by linarith)] at this
    have ha1 : a < 1 := by
      have := hmin A0 hA0c
      have : ((A0.card : ℝ) - SumOver x A0) / ((A0.card : ℝ) - r1 A0) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      linarith
    have ha0 : 0 < a := by
      have := hK2 B0 hB0c
      by_contra hc; push_neg at hc
      nlinarith
    clear_value a
    obtain ⟨hP1, hbx1, hbx2⟩ := mr_side r1 hr1.2.2 x hx a ha0 ha1 hK1
    have hb0 : 0 < 1 - a := by linarith
    have hb1 : 1 - a < 1 := by linarith
    obtain ⟨hP2, hby2, hby1⟩ := mr_side r2 hr2.2.2 y hy (1 - a) hb0 hb1 hK2
    have e11 : (1:ℝ) - (1 - a) = a := by ring
    rw [e11] at hby1
    set x1 : Fin m → ℝ := fun i => max 0 (1 - (1 - x i) / a) with hx1
    set y2 : Fin n → ℝ := fun j => max 0 (1 - (1 - y j) / (1 - a)) with hy2
    have hZ1 : (x1, fun j => (y j - (1 - a) * y2 j) / a) ∈ ZDisjoint r1 r2 :=
      ⟨hbx1, hby1, Or.inl hP1⟩
    have hZ2 : (fun i => (x i - a * x1 i) / (1 - a), y2) ∈ ZDisjoint r1 r2 :=
      ⟨hbx2, hby2, Or.inr hP2⟩
    have hmem := (convex_convexHull ℝ (ZDisjoint r1 r2)) (subset_convexHull ℝ _ hZ1)
      (subset_convexHull ℝ _ hZ2) ha0.le hb0.le (by ring)
    convert hmem using 1
    ext i
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

end Disjunctive.Polymatroids

open Disjunctive.Polymatroids


theorem solution {m n : ℕ} (r1 : Finset (Fin m) → ℝ)
    (r2 : Finset (Fin n) → ℝ) (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ (ZDisjoint r1 r2) =
      {p : (Fin m → ℝ) × (Fin n → ℝ) | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 1) ∧
        (∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1) ∧
        ∀ A : Finset (Fin m), ∀ B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
          1 ≤ ((A.card : ℝ) - SumOver p.1 A) / ((A.card : ℝ) - r1 A) +
            ((B.card : ℝ) - SumOver p.2 B) / ((B.card : ℝ) - r2 B)} := by
  exact mr_core r1 r2 hr1 hr2
