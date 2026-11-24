-- Prove2me | solution 1 for DenseProdQSAT.Testing.gram_rank
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:36:09.362894+00:00
-- url     : https://prove2.me/submissions/d5718dd8-96d8-43f9-8892-cd03c3485ac9

import Definitions.Def_DenseProdQSAT_Testing_Algebra
set_option autoImplicit false
open DenseProdQSAT.Testing
open scoped ComplexOrder
open Matrix


private lemma gr_sub_eq {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (I : Finset (Fin q)) :
    (M.conjTranspose * M).submatrix (fun i : I => i.val) (fun i : I => i.val) =
      (M.submatrix id (fun i : I => i.val))ᴴ * M.submatrix id (fun i : I => i.val) := by
  ext i j; simp [Matrix.mul_apply]

private lemma gr_det_ne_zero_iff {p : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin p) ι ℂ) : (Nᴴ * N).det ≠ 0 ↔ LinearIndependent ℂ N.col := by
  rw [← (posSemidef_conjTranspose_mul_self N).posDef_iff_det_ne_zero,
    (posSemidef_conjTranspose_mul_self N).posDef_iff_isUnit, ← mulVec_injective_iff_isUnit,
    ← mulVec_injective_iff]
  constructor <;> intro h x y hxy
  · apply h
    rw [← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_mulVec]
  · have : (Nᴴ * N) *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
    rw [conjTranspose_mul_self_mulVec_eq_zero, mulVec_sub, sub_eq_zero] at this
    exact h this

private lemma gr_card_le {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (I : Finset (Fin q))
    (h : LinearIndependent ℂ (M.submatrix id (fun i : I => i.val)).col) : I.card ≤ M.rank := by
  have h1 := rank_submatrix_le M id (fun i : I => i.val)
  rw [rank_eq_finrank_span_cols, ← Set.finrank,
    ← linearIndependent_iff_card_eq_finrank_span.mp h] at h1
  simpa using h1

private lemma gr_exists {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (r : ℕ) (hr : r ≤ M.rank) :
    ∃ I : Finset (Fin q), I.card = r ∧
      LinearIndependent ℂ (M.submatrix id (fun i : I => i.val)).col := by
  classical
  obtain ⟨b, -, -, hspan, hli⟩ := exists_linearIndepOn_extension (K := ℂ) (v := M.col)
    (linearIndepOn_empty ℂ M.col) (Set.empty_subset Set.univ)
  have hcard : b.toFinset.card = M.rank := by
    rw [rank_eq_finrank_span_cols]
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli
    have h2 : Submodule.span ℂ (Set.range (fun x : b => M.col x)) =
        Submodule.span ℂ (Set.range M.col) := by
      apply le_antisymm
      · apply Submodule.span_mono
        rintro _ ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        have := hspan ⟨x, Set.mem_univ _, rfl⟩
        rwa [← Set.image_eq_range] at *
    rw [Set.toFinset_card, h1, Set.finrank, h2]
  obtain ⟨I, hIb, hIc⟩ := Finset.exists_subset_card_eq (s := b.toFinset) (n := r) (by omega)
  refine ⟨I, hIc, ?_⟩
  have : LinearIndepOn ℂ M.col (I : Set (Fin q)) := hli.mono (by
    intro x hx; simpa using hIb hx)
  exact this

theorem solution {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) :
    GramSum M 0 = 1 ∧ GramSum M (q + 1) = 0 ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ q →
        (GramSum M r).im = 0 ∧ (0 < (GramSum M r).re ↔ r ≤ M.rank) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [GramSum]
  · unfold GramSum
    rw [Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty]
  · intro r _ _
    have hS : GramSum M r = ∑ I ∈ (Finset.univ : Finset (Fin q)).powersetCard r,
        ((M.submatrix id (fun i : I => i.val))ᴴ * M.submatrix id (fun i : I => i.val)).det := by
      unfold GramSum
      exact Finset.sum_congr rfl fun I _ => by rw [gr_sub_eq]
    have hnn : ∀ I ∈ (Finset.univ : Finset (Fin q)).powersetCard r,
        (0 : ℂ) ≤ ((M.submatrix id (fun i : I => i.val))ᴴ *
          M.submatrix id (fun i : I => i.val)).det :=
      fun I _ => (posSemidef_conjTranspose_mul_self _).det_nonneg
    have hpos : 0 ≤ GramSum M r := hS ▸ Finset.sum_nonneg hnn
    have him : (GramSum M r).im = 0 := (Complex.nonneg_iff.mp hpos).2.symm
    refine ⟨him, ?_⟩
    have hre : 0 < (GramSum M r).re ↔ GramSum M r ≠ 0 := by
      constructor
      · intro h h0; rw [h0] at h; simp at h
      · intro h
        rcases (Complex.nonneg_iff.mp hpos).1.lt_or_eq with h1 | h1
        · exact h1
        · exact absurd (Complex.ext (by simp [← h1]) (by simp [him])) h
    rw [hre, hS, Ne, Finset.sum_eq_zero_iff_of_nonneg hnn]
    push Not
    constructor
    · rintro ⟨I, hI, hd⟩
      rw [Finset.mem_powersetCard] at hI
      rw [← hI.2]
      exact gr_card_le M I ((gr_det_ne_zero_iff _).mp hd)
    · intro hr
      obtain ⟨I, hIc, hli⟩ := gr_exists M r hr
      exact ⟨I, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hIc⟩,
        (gr_det_ne_zero_iff _).mpr hli⟩
