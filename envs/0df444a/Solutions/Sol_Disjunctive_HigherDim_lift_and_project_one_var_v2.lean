-- Prove2me | solution 1 for Disjunctive.HigherDim.lift_and_project_one_var_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:37:31.662027+00:00
-- url     : https://prove2.me/submissions/9f2a8913-dc2a-4b47-b1b5-493147e25874

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows



namespace Disjunctive.HigherDim

lemma hd_row_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (k : Fin n) (c : ℝ)
    (hi : A i = Pi.single k c) (x : Fin n → ℝ) : (A.mulVec x) i = c * x k := by
  simp [Matrix.mulVec, dotProduct, hi, Pi.single_apply]

lemma hd_poly_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {Nprime : Finset (Fin n)} (hK : HasBoundRows A b Nprime) {x : Fin n → ℝ}
    (hx : x ∈ Poly A b) (k : Fin n) : 0 ≤ x k := by
  obtain ⟨i, hi, hb⟩ := hK.1 k
  have := hx i
  rw [hd_row_single A i k 1 hi, hb] at this
  linarith

lemma hd_poly_le_one {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    {Nprime : Finset (Fin n)} (hK : HasBoundRows A b Nprime) {x : Fin n → ℝ}
    (hx : x ∈ Poly A b) (k : Fin n) (hk : k ∈ Nprime) : x k ≤ 1 := by
  obtain ⟨i, hi, hb⟩ := hK.2 k hk
  have hi' : A i = Pi.single k (-1) := by rw [hi, Pi.single_neg]
  have := hx i
  rw [hd_row_single A i k (-1) hi', hb] at this
  linarith

lemma hd_poly_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (Poly A b) := by
  intro x hx y hy a c ha hc hac i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hx i) ha
  have h2 := mul_le_mul_of_nonneg_left (hy i) hc
  have : b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
  linarith

lemma hd_face_slice {n : ℕ} (T : Set (Fin n → ℝ)) (k : Fin n) (c s : ℝ) (hs : s ≠ 0)
    (h : ∀ z ∈ T, 0 ≤ s * (z k - c)) :
    convexHull ℝ T ∩ {x | x k = c} ⊆ convexHull ℝ (T ∩ {x | x k = c}) := by
  classical
  rintro x ⟨hx, hxk⟩
  rw [mem_convexHull_iff_exists_fintype] at hx
  obtain ⟨ι, _, w, z, hw0, hw1, hz, rfl⟩ := hx
  have hsum : ∑ i, w i * (s * (z i k - c)) = 0 := by
    have e : (∑ i, w i • z i) k = ∑ i, w i * z i k := by simp [Finset.sum_apply]
    simp only [Set.mem_setOf_eq] at hxk
    have e2 : ∑ i, w i * (s * (z i k - c)) = s * (∑ i, w i * z i k) - s * c * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1; ext i; ring
    rw [e2, ← e, hxk, hw1]; ring
  have hterm :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw0 i) (h _ (hz i)))).1 hsum
  rw [← Finset.centerMass_eq_of_sum_1 _ _ hw1, ← Finset.centerMass_filter_ne_zero]
  apply Finset.centerMass_mem_convexHull
  · intro i _; exact hw0 i
  · rw [Finset.sum_filter_ne_zero, hw1]; norm_num
  · intro i hi
    simp only [Finset.mem_filter] at hi
    refine ⟨hz i, ?_⟩
    have := hterm i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hi.2
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hs
      · show z i k = c; linarith

lemma hd_conv_slice {n : ℕ} (T : Set (Fin n → ℝ)) (k : Fin n) (h0 : ∀ z ∈ T, 0 ≤ z k)
    (h1 : ∀ z ∈ T, z k ≤ 1) :
    convexHull ℝ (convexHull ℝ T ∩ ZeroOneSet k) = convexHull ℝ (T ∩ ZeroOneSet k) := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull _ _)
    rintro x ⟨hx, hk | hk⟩
    · have := hd_face_slice T k 0 1 one_ne_zero (by intro z hz; simpa using h0 z hz) ⟨hx, hk⟩
      exact convexHull_mono (Set.inter_subset_inter_right _ (fun y hy => Or.inl hy)) this
    · have := hd_face_slice T k 1 (-1) (by norm_num)
        (by intro z hz; have := h1 z hz; linarith) ⟨hx, hk⟩
      exact convexHull_mono (Set.inter_subset_inter_right _ (fun y hy => Or.inr hy)) this
  · exact convexHull_mono (Set.inter_subset_inter_left _ (subset_convexHull ℝ T))

lemma hd_pj_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    Convex ℝ (Pj A b j) := by
  rintro x ⟨y, hy⟩ x' ⟨y', hy'⟩ a c ha hc hac
  refine ⟨a • y + c • y', ?_, ?_, ?_⟩
  · intro i
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_nonneg ha (hy.1 i)
    have h2 := mul_nonneg hc (hy'.1 i)
    have : b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
    nlinarith
  · intro i
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_nonneg ha (hy.2.1 i)
    have h2 := mul_nonneg hc (hy'.2.1 i)
    nlinarith
  · have e1 : y j = x j := hy.2.2
    have e2 : y' j = x' j := hy'.2.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2]

theorem hd_pj_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (j : Fin n) (hj : j ∈ Nprime) :
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by
  apply le_antisymm
  · rintro x ⟨y, h1, h2, h3⟩
    -- bounds on x j
    have hl0 : 0 ≤ x j := by
      obtain ⟨i, hi, hb⟩ := hK.1 j
      have := h2 i
      rw [hd_row_single A i j 1 hi, hb] at this
      simp only at h3
      linarith
    have hl1 : x j ≤ 1 := by
      obtain ⟨i, hi, hb⟩ := hK.2 j hj
      have hi' : A i = Pi.single j (-1) := by rw [hi, Pi.single_neg]
      have := h1 i
      rw [hd_row_single A i j (-1) hi', hd_row_single A i j (-1) hi', hb] at this
      simp only at h3
      linarith
    simp only at h1 h2 h3
    rcases eq_or_lt_of_le hl0 with h0 | h0
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inl h0.symm⟩
      have := h1 i; have := h2 i; rw [← h0] at *; linarith
    rcases eq_or_lt_of_le hl1 with h1' | h1'
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inr h1'⟩
      have := h1 i; have := h2 i; rw [h1'] at *; linarith
    set l := x j with hl
    have hxeq : x = (1 - l) • ((1 - l)⁻¹ • (x - y)) + l • (l⁻¹ • y) := by
      rw [smul_smul, smul_smul, mul_inv_cancel₀ (by linarith), mul_inv_cancel₀ (by linarith),
        one_smul, one_smul, sub_add_cancel]
    rw [hxeq]
    apply convex_convexHull ℝ _ _ _ (by linarith) h0.le (by ring)
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inl ?_⟩
      · simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul]
        rw [le_inv_mul_iff₀ (by linarith)]
        have := h1 i
        nlinarith
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← h3, ← hl, sub_self, mul_zero]
    · apply subset_convexHull
      refine ⟨fun i => ?_, Or.inr ?_⟩
      · simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        rw [le_inv_mul_iff₀ h0]
        have := h2 i
        nlinarith
      · simp only [Pi.smul_apply, smul_eq_mul, h3, ← hl]
        exact inv_mul_cancel₀ h0.ne'
  · apply convexHull_min _ (hd_pj_convex A b j)
    rintro x ⟨hx, hxj | hxj⟩
    · refine ⟨0, fun i => ?_, fun i => ?_, ?_⟩
      · simp only [Matrix.mulVec_zero, Pi.zero_apply, hxj]; have := hx i; linarith
      · simp [hxj]
      · simp [hxj]
    · refine ⟨x, fun i => ?_, fun i => ?_, rfl⟩
      · simp [hxj]
      · simp only [hxj, mul_one]; have := hx i; linarith

theorem hd_ls_one_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) :
    ∀ j ∈ Nprime, NOp A b Nprime ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by
  intro j hj x ⟨Y, hY⟩
  rw [← hd_pj_core A b Nprime hK j hj]
  exact ⟨fun k => Y k j, (hY.2.2 j hj).1, (hY.2.2 j hj).2, hY.2.1 j hj⟩

theorem hd_iter_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (l : List (Fin n))
    (hl : ∀ j ∈ l, j ∈ Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (Poly A b ∩ ⋂ j ∈ l.toFinset, ZeroOneSet j) := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [IteratedSplit, List.foldl_nil, List.toFinset_nil, Finset.notMem_empty,
      Set.iInter_of_empty, Set.iInter_univ, Set.inter_univ]
    exact (hd_poly_convex A b).convexHull_eq.symm
  | append_singleton l k ih =>
    have ih' := ih (fun j hj => hl j (by simp [hj]))
    have hk : k ∈ Nprime := hl k (by simp)
    unfold IteratedSplit at ih' ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih']
    unfold SplitConvexify
    rw [hd_conv_slice]
    · congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, List.mem_toFinset, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun j hj => hj.elim (h2 j) (fun e => e ▸ h3)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun j hj => h2 j (Or.inl hj)⟩, h2 k (Or.inr rfl)⟩
    · intro z hz; exact hd_poly_nonneg hK hz.1 k
    · intro z hz; exact hd_poly_le_one hK hz.1 k hk

theorem hd_full_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (l : List (Fin n))
    (heq : l.toFinset = Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (K0Set A b Nprime) := by
  rw [hd_iter_core A b Nprime hK l (fun j hj => heq ▸ List.mem_toFinset.2 hj), heq]
  rfl

end Disjunctive.HigherDim

open Disjunctive.HigherDim


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (j : Fin n) (hj : j ∈ Nprime) :
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by
  exact hd_pj_core A b Nprime hK j hj
