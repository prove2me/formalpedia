-- Prove2me | solution 1 for Finset.graph_high_degree_subset_lb
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:42.760932+00:00
-- url     : https://prove2.me/submissions/e605149a-d3b4-49e8-b91c-8d71d15dd9f5

import Mathlib

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    (δ / 2) * (A.card : ℝ) ≤
      ((A.filter (fun a ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ))).card : ℝ) ∧
    (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤
      ((E.filter (fun p : G × G ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))).card : ℝ) := by
  classical
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  set Apop : Finset G := A.filter (fun a ↦ (δ / 2) * (B.card : ℝ) ≤ (rowDeg a : ℝ))
    with hApop_def
  set Epop : Finset (G × G) := E.filter (fun p : G × G ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))
    with hEpop_def
  have hApop_sub : Apop ⊆ A := Finset.filter_subset _ _
  have hEpop_sub : Epop ⊆ E := Finset.filter_subset _ _
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_pos
  have hBcard_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hAB.symm
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard_eq]; exact hA_pos
  have hB_nn : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_pos
  have hrowDeg_le : ∀ a, rowDeg a ≤ B.card := fun a ↦
    Finset.card_le_card (Finset.filter_subset _ _)
  have hrowDeg_le_R : ∀ a, (rowDeg a : ℝ) ≤ (B.card : ℝ) := fun a ↦ by
    exact_mod_cast hrowDeg_le a
  have hSumRow : ∑ a ∈ A, (rowDeg a : ℕ) = E.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ A, rowDeg a = ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 :
        ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) = ((A ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (A ×ˢ B).filter (· ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [step2, step3, step4]
  have hSumRow_real : ∑ a ∈ A, (rowDeg a : ℝ) = (E.card : ℝ) := by
    have h := hSumRow
    have hcast : ((∑ a ∈ A, rowDeg a : ℕ) : ℝ) = (E.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hsplit_A : ∑ a ∈ A, (rowDeg a : ℝ) =
      (∑ a ∈ Apop, (rowDeg a : ℝ)) + ∑ a ∈ A \ Apop, (rowDeg a : ℝ) := by
    rw [← Finset.sum_sdiff hApop_sub]; ring
  have hrare : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤
      ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    rw [show ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) =
              ∑ _a ∈ A \ Apop, ((δ / 2) * (B.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hApop_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨ha.1, le_of_lt hgt⟩
  have hAdiff_le_A : ((A \ Apop).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := A) (t := Apop))
  have hδ2B_nn : 0 ≤ (δ / 2) * (B.card : ℝ) := by positivity
  have hrare' : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤ (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hAdiff_le_A hδ2B_nn
    linarith [hrare]
  have hSumApop : ∑ a ∈ Apop, (rowDeg a : ℕ) = Epop.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ Apop, rowDeg a = ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 : ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) =
        ((Apop ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (Apop ×ˢ B).filter (· ∈ E) = Epop := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, hEpop_def, hApop_def, hrowDeg_def]
      constructor
      · rintro ⟨⟨⟨hp1A, hp1pop⟩, _hp2⟩, hpE⟩
        exact ⟨hpE, hp1pop⟩
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨⟨⟨hpAB.1, hpop⟩, hpAB.2⟩, hpE⟩
    rw [step2, step3, step4]
  have hSumApop_real : ∑ a ∈ Apop, (rowDeg a : ℝ) = (Epop.card : ℝ) := by
    have h := hSumApop
    have hcast : ((∑ a ∈ Apop, rowDeg a : ℕ) : ℝ) = (Epop.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hE_dense' : δ * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ A, (rowDeg a : ℝ) := by
    rw [hSumRow_real]; exact hE_dense
  have hEpop_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Epop.card : ℝ) := by
    have : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ Apop, (rowDeg a : ℝ) := by
      have hδ_split : δ * (A.card : ℝ) * (B.card : ℝ) =
          (δ / 2) * (A.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
        ring
      linarith [hE_dense', hsplit_A, hrare', hδ_split]
    linarith [this, hSumApop_real]
  have hApop_sum_ub : ∑ a ∈ Apop, (rowDeg a : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
    rw [show (Apop.card : ℝ) * (B.card : ℝ) = ∑ _a ∈ Apop, (B.card : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a _ ↦ hrowDeg_le_R a
  have hApop_lb : (δ / 2) * (A.card : ℝ) ≤ (Apop.card : ℝ) := by
    have h1 : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
      calc (δ / 2) * (A.card : ℝ) * (B.card : ℝ)
          ≤ (Epop.card : ℝ) := hEpop_lb
        _ = ∑ a ∈ Apop, (rowDeg a : ℝ) := hSumApop_real.symm
        _ ≤ (Apop.card : ℝ) * (B.card : ℝ) := hApop_sum_ub
    exact le_of_mul_le_mul_right h1 hB_pos
  exact ⟨hApop_lb, hEpop_lb⟩
