-- Prove2me | solution 1 for Disjunctive.SequentialConvex.sequential_convexification_facial
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:00:02.742605+00:00
-- url     : https://prove2.me/submissions/af0cbe6e-b5ae-48e0-bf5d-cd39027713a6

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic
import Definitions.Def_Disjunctive_SequentialConvex_Fseq



namespace Disjunctive.SequentialConvex

lemma sc_extreme_hull {n : ℕ} {A F T : Set (Fin n → ℝ)} (hF : IsExtreme ℝ A F)
    (hTA : T ⊆ A) (hA : Convex ℝ A) :
    convexHull ℝ T ∩ F ⊆ convexHull ℝ (T ∩ F) := by
  let G : Set (Fin n → ℝ) := convexHull ℝ (T ∩ F) ∪ (convexHull ℝ T \ F)
  have hCA : convexHull ℝ T ⊆ A := convexHull_min hTA hA
  have hGT : G ⊆ convexHull ℝ T := by
    intro x hx
    change x ∈ convexHull ℝ (T ∩ F) ∪ (convexHull ℝ T \ F) at hx
    rcases hx with hx | hx
    · exact convexHull_mono Set.inter_subset_left hx
    · exact hx.1
  have hG : Convex ℝ G := by
    rw [convex_iff_openSegment_subset]
    intro x hx y hy z hz
    have hzT : z ∈ convexHull ℝ T :=
      (convex_convexHull ℝ T).openSegment_subset (hGT hx) (hGT hy) hz
    by_cases hzF : z ∈ F
    · have hxF := hF.left_mem_of_mem_openSegment (hCA (hGT hx)) (hCA (hGT hy)) hzF hz
      have hyF := hF.right_mem_of_mem_openSegment (hCA (hGT hx)) (hCA (hGT hy)) hzF hz
      change x ∈ convexHull ℝ (T ∩ F) ∪ (convexHull ℝ T \ F) at hx
      change y ∈ convexHull ℝ (T ∩ F) ∪ (convexHull ℝ T \ F) at hy
      have hx' : x ∈ convexHull ℝ (T ∩ F) := by
        rcases hx with hx | hx
        · exact hx
        · exact absurd hxF hx.2
      have hy' : y ∈ convexHull ℝ (T ∩ F) := by
        rcases hy with hy | hy
        · exact hy
        · exact absurd hyF hy.2
      exact Or.inl ((convex_convexHull ℝ _).openSegment_subset hx' hy' hz)
    · exact Or.inr ⟨hzT, hzF⟩
  have hTG : T ⊆ G := by
    intro x hx
    by_cases hxF : x ∈ F
    · exact Or.inl (subset_convexHull ℝ _ ⟨hx, hxF⟩)
    · exact Or.inr ⟨subset_convexHull ℝ _ hx, hxF⟩
  rintro x ⟨hx, hxF⟩
  rcases convexHull_min hTG hG hx with h | h
  · exact h
  · exact absurd hxF h.2

lemma sc_F0_convex {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (F0Set A b) := by
  intro x hx y hy a c ha hc hac
  refine ⟨fun i => ?_, ?_⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hx.1 i
    have h2 := hy.1 i
    have e : b i = a * b i + c * b i := by rw [← add_mul, hac, one_mul]
    have := mul_le_mul_of_nonneg_left h1 ha
    have := mul_le_mul_of_nonneg_left h2 hc
    linarith
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 := hx.2 i
    have h2 := hy.2 i
    simp only [Pi.zero_apply] at h1 h2
    positivity

theorem sc_core {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ)
    (σ : Fin (Fintype.card S) ≃ S) (hFacial : Facial A b Qidx d d0) :
    Fseq Qidx (F0Set A b) d d0 σ (Fintype.card S) =
      convexHull ℝ (DisjunctiveConstraintSet A b Qidx d d0) := by
  let Fp : ℕ → Set (Fin n → ℝ) := fun k => F0Set A b ∩
    {x | ∀ t : Fin (Fintype.card S), t.val < k → ∃ i, d0 (σ t) i ≤ dotProduct (d (σ t) i) x}
  have hFpA : ∀ k, Fp k ⊆ F0Set A b := fun k => Set.inter_subset_left
  have key : ∀ k, k ≤ Fintype.card S → Fseq Qidx (F0Set A b) d d0 σ k = convexHull ℝ (Fp k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : Fp 0 = F0Set A b := by
        ext x
        simp [Fp]
      rw [this, (sc_F0_convex A b).convexHull_eq]
      rfl
    | succ k ih =>
      intro hk
      have hk' : k < Fintype.card S := hk
      have ih' := ih hk'.le
      simp only [Fseq, dif_pos hk']
      rw [ih']
      apply Set.Subset.antisymm
      · apply convexHull_min _ (convex_convexHull ℝ _)
        intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨i, hx⟩ := hx
        have h1 := sc_extreme_hull (hFacial (σ ⟨k, hk'⟩) i) (hFpA k) (sc_F0_convex A b)
          ⟨hx.1, (hFpA k) |> fun _ => ?_, hx.2⟩
        · refine convexHull_mono ?_ h1
          rintro y ⟨hy, -, hyH⟩
          refine ⟨hy.1, fun t ht => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
          · exact hy.2 t ht
          · have : t = ⟨k, hk'⟩ := Fin.ext ht
            subst this
            exact ⟨i, hyH⟩
        · exact convexHull_min (hFpA k) (sc_F0_convex A b) hx.1
      · apply convexHull_mono
        intro x hx
        obtain ⟨i, hi⟩ := hx.2 ⟨k, hk'⟩ (Nat.lt_succ_self k)
        simp only [Set.mem_iUnion]
        refine ⟨i, ⟨subset_convexHull ℝ _ ⟨hx.1, fun t ht => hx.2 t (Nat.lt_succ_of_lt ht)⟩, hi⟩⟩
  rw [key _ le_rfl]
  congr 1
  ext x
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun j => ?_⟩
    obtain ⟨t, rfl⟩ := σ.surjective j
    exact h t t.isLt
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun t _ => h (σ t)⟩

end Disjunctive.SequentialConvex

open Disjunctive.SequentialConvex


theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ)
    (σ : Fin (Fintype.card S) ≃ S) (hFacial : Facial A b Qidx d d0) :
    Fseq Qidx (F0Set A b) d d0 σ (Fintype.card S) =
      convexHull ℝ (DisjunctiveConstraintSet A b Qidx d d0) := by
  exact sc_core A b Qidx d d0 σ hFacial
