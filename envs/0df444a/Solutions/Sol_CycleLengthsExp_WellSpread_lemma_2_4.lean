-- Prove2me | solution 1 for CycleLengthsExp.WellSpread.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:46:58.056741+00:00
-- url     : https://prove2.me/submissions/312a7176-8e32-426e-9047-781a3a68a093

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

set_option autoImplicit false
open CycleLengthsExp.WellSpread

theorem clw_preimage_le (n r : ℕ) (f : Fin n → Fin r) (C : ℝ)
    (hfib : ∀ i : Fin r, ((f ⁻¹' {i}).ncard : ℝ) ≤ C) (S : Set (Fin r)) :
    ((f ⁻¹' S).ncard : ℝ) ≤ C * S.ncard := by
  classical
  have hS : S.Finite := Set.toFinite _
  let S' := hS.toFinset
  have e1 : f ⁻¹' S = ↑(S'.biUnion (fun i => (Finset.univ.filter (fun x => f x = i)))) := by
    ext x
    simp [S']
  have e2 : S.ncard = S'.card := Set.ncard_eq_toFinset_card S hS
  rw [e1, Set.ncard_coe_finset, e2]
  have h1 : (S'.biUnion (fun i => (Finset.univ.filter (fun x => f x = i)))).card ≤
      ∑ i ∈ S', (Finset.univ.filter (fun x => f x = i)).card := Finset.card_biUnion_le
  have h2 : ∀ i : Fin r, (((Finset.univ.filter (fun x => f x = i)).card : ℕ) : ℝ) ≤ C := by
    intro i
    have : (f ⁻¹' {i}) = ↑(Finset.univ.filter (fun x => f x = i)) := by ext x; simp
    have h := hfib i
    rw [this, Set.ncard_coe_finset] at h
    exact h
  calc (((S'.biUnion (fun i => (Finset.univ.filter (fun x => f x = i)))).card : ℕ) : ℝ)
      ≤ ((∑ i ∈ S', (Finset.univ.filter (fun x => f x = i)).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ i ∈ S', (((Finset.univ.filter (fun x => f x = i)).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _i ∈ S', C := Finset.sum_le_sum (fun i _ => h2 i)
    _ = C * S'.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem clw_lemma_2_4 (n r : ℕ) (G : SimpleGraph (Fin n)) (k α C : ℝ)
    (hk : 0 < k) (hα : 0 < α) (hC : 0 < C) (hG : IsKAlphaExpander k α G)
    (f : Fin n → Fin r) (hf : Function.Surjective f)
    (hfib : ∀ i : Fin r, ((f ⁻¹' {i}).ncard : ℝ) ≤ C) :
    (n : ℝ) / C ≤ r ∧ IsKAlphaExpander (k / C) (α / C) (contract G f) := by
  constructor
  · have h := clw_preimage_le n r f C hfib Set.univ
    rw [Set.preimage_univ, Set.ncard_univ, Set.ncard_univ] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    rw [div_le_iff₀ hC]
    linarith
  · intro U' hU'
    set U : Set (Fin n) := f ⁻¹' U' with hU
    have hUc : (U.ncard : ℝ) ≤ C * U'.ncard := clw_preimage_le n r f C hfib U'
    have hUk : (U.ncard : ℝ) ≤ k := by
      have : (U'.ncard : ℝ) ≤ k / C := hU'
      rw [le_div_iff₀ hC] at this
      linarith
    have hUU : (U'.ncard : ℝ) ≤ U.ncard := by
      have h1 : U' ⊆ f '' U := by
        intro i hi
        obtain ⟨x, rfl⟩ := hf i
        exact ⟨x, hi, rfl⟩
      have h2 : U'.ncard ≤ (f '' U).ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
      have h3 : (f '' U).ncard ≤ U.ncard := Set.ncard_image_le (Set.toFinite _)
      exact_mod_cast h2.trans h3
    have hexp := hG U hUk
    have hsub : f '' (extNbhd G U) ⊆ extNbhd (contract G f) U' := by
      rintro _ ⟨w, ⟨hwU, u, huU, hadj⟩, rfl⟩
      have hfw : f w ∉ U' := hwU
      have hfu : f u ∈ U' := huU
      refine ⟨hfw, f u, hfu, ?_⟩
      refine ⟨fun h => hfw (h ▸ hfu), u, w, rfl, rfl, hadj⟩
    have hN : ((extNbhd G U).ncard : ℝ) ≤ C * (f '' extNbhd G U).ncard := by
      have h1 := clw_preimage_le n r f C hfib (f '' extNbhd G U)
      have h2 : (extNbhd G U).ncard ≤ (f ⁻¹' (f '' extNbhd G U)).ncard :=
        Set.ncard_le_ncard (Set.subset_preimage_image _ _) (Set.toFinite _)
      have h3 : ((extNbhd G U).ncard : ℝ) ≤ ((f ⁻¹' (f '' extNbhd G U)).ncard : ℝ) := by exact_mod_cast h2
      linarith
    have hN2 : ((f '' extNbhd G U).ncard : ℝ) ≤ (extNbhd (contract G f) U').ncard := by
      exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    -- goal: α / C * |U'| ≤ |N'(U')|
    have key : α * U'.ncard ≤ C * (extNbhd (contract G f) U').ncard := by
      have : (U'.ncard : ℝ) * α ≤ U.ncard * α := mul_le_mul_of_nonneg_right hUU hα.le
      nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    linarith

theorem solution (n r : ℕ) (G : SimpleGraph (Fin n)) (k α C : ℝ)
    (hk : 0 < k) (hα : 0 < α) (hC : 0 < C) (hG : IsKAlphaExpander k α G)
    (f : Fin n → Fin r) (hf : Function.Surjective f)
    (hfib : ∀ i : Fin r, ((f ⁻¹' {i}).ncard : ℝ) ≤ C) :
    (n : ℝ) / C ≤ r ∧ IsKAlphaExpander (k / C) (α / C) (contract G f) :=
  clw_lemma_2_4 n r G k α C hk hα hC hG f hf hfib
