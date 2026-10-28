-- Prove2me | solution 1 for EssCheck.Accuracy.welfare_formula
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:51:06.131181+00:00
-- url     : https://prove2.me/submissions/69d1cdb9-6903-4d44-9bfb-f0321760d037

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

open EssCheck.Accuracy in
theorem solution {n : ℕ} (M : Model n) (hS : M.Standing)
    (β x : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (∀ i, IsHybrid M β x i → 0 < M.p0 i →
      yAt M β x i =
        x * M.pH i * M.l i /
          ((1 - β) * (1 - x) * M.p0 i * (M.αbar * M.v i - M.l i))) ∧
    welfare M β x =
      x * ((∑ i ∈ hybridSet M β x,
        M.pH i * (M.v i - 2 * zt M i * M.l i *
          (M.αbar * M.v i / (M.αbar * M.v i - M.l i)))) +
        (∑ i ∈ Finset.univ \ hybridSet M β x, M.pH i * M.v i)) +
      (1 - x) * ((∑ i ∈ hybridSet M β x, M.p0 i * M.v i) +
        (∑ i ∈ Finset.univ \ hybridSet M β x, M.p0 i * M.v i)) - M.c x := by
  obtain ⟨hpH, -, hp0, -, -, hl, hlv, -⟩ := hS
  have hyb_y : ∀ i, IsHybrid M β x i →
      yAt M β x i = lamC M β x i / (1 - lamC M β x i) * (M.l i / (M.αbar * M.v i - M.l i)) := by
    intro i h
    unfold yAt yOf
    exact if_pos h
  have hyb_z : ∀ i, IsHybrid M β x i → zAt M β x i = zt M i := by
    intro i h
    unfold zAt zOf
    exact if_pos h
  have non_y : ∀ i, ¬ IsHybrid M β x i → yAt M β x i = 1 := by
    intro i h
    unfold yAt yOf
    exact if_neg h
  have non_z : ∀ i, ¬ IsHybrid M β x i → zAt M β x i = 0 := by
    intro i h
    unfold zAt zOf
    exact if_neg h
  have h1β : 0 < 1 - β := by linarith
  have h1x : 0 < 1 - x := by linarith
  have part1 : ∀ i, IsHybrid M β x i → 0 < M.p0 i →
      yAt M β x i = x * M.pH i * M.l i /
          ((1 - β) * (1 - x) * M.p0 i * (M.αbar * M.v i - M.l i)) := by
    intro i h hp
    rw [hyb_y i h]
    have hd : 0 < M.αbar * M.v i - M.l i := by linarith [hlv i]
    have hden : 0 < x * M.pH i + (1 - β) * (1 - x) * M.p0 i := by
      have := mul_nonneg hx0.le (hpH.1 i)
      have : 0 < (1 - β) * (1 - x) * M.p0 i := by positivity
      linarith
    unfold lamC
    have hq : 1 - x * M.pH i / (x * M.pH i + (1 - β) * (1 - x) * M.p0 i)
        = (1 - β) * (1 - x) * M.p0 i / (x * M.pH i + (1 - β) * (1 - x) * M.p0 i) := by
      field_simp; ring
    rw [hq]
    have : (1 - β) * (1 - x) * M.p0 i ≠ 0 := by positivity
    field_simp
  refine ⟨part1, ?_⟩
  -- key relation for hybrid indices
  have hkey : ∀ i, IsHybrid M β x i →
      (1 - x) * (1 - β) * M.p0 i * yAt M β x i
        = x * M.pH i * (M.l i / (M.αbar * M.v i - M.l i)) := by
    intro i h
    have hd : 0 < M.αbar * M.v i - M.l i := by linarith [hlv i]
    rcases (hp0.1 i).lt_or_eq with hp | hp
    · rw [part1 i h hp]
      field_simp
    · -- p0 i = 0 forces pH i = 0
      have hpH0 : M.pH i = 0 := by
        rcases (hpH.1 i).lt_or_eq with hq | hq
        · exfalso
          have hlam : lamC M β x i = 1 := by
            unfold lamC; rw [← hp]; simp only [mul_zero, add_zero]
            have : 0 < x * M.pH i := mul_pos hx0 hq
            field_simp
          have := h
          unfold IsHybrid IsHybridAt at this
          rw [hlam] at this
          linarith [hl i]
        · exact hq.symm
      rw [← hp, hpH0]; ring
  have hmem : ∀ i, i ∈ hybridSet M β x ↔ IsHybrid M β x i := by
    classical
    intro i
    unfold hybridSet
    simp
  -- per-index identity
  set g : Fin n → ℝ := fun i =>
    x * (M.pH i * surpH M β x i) + (1 - x) * (M.p0 i * (β * M.v i + (1 - β) * surpL M β x i))
    with hg
  have hW : x * wH M β x + (1 - x) * wL M β x = ∑ i, g i := by
    unfold wH wL
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  set S := hybridSet M β x with hSdef
  have hR : x * ((∑ i ∈ S, M.pH i * (M.v i - 2 * zt M i * M.l i *
          (M.αbar * M.v i / (M.αbar * M.v i - M.l i)))) +
        (∑ i ∈ Finset.univ \ S, M.pH i * M.v i)) +
      (1 - x) * ((∑ i ∈ S, M.p0 i * M.v i) + (∑ i ∈ Finset.univ \ S, M.p0 i * M.v i))
      = (∑ i ∈ S, g i) + ∑ i ∈ Finset.univ \ S, g i := by
    have hS1 : ∀ i ∈ S, g i = x * (M.pH i * (M.v i - 2 * zt M i * M.l i *
          (M.αbar * M.v i / (M.αbar * M.v i - M.l i)))) + (1 - x) * (M.p0 i * M.v i) := by
      intro i hi
      have h := (hmem i).mp hi
      have hd : 0 < M.αbar * M.v i - M.l i := by linarith [hlv i]
      have hk := hkey i h
      have hfrac : M.αbar * M.v i / (M.αbar * M.v i - M.l i)
          = 1 + M.l i / (M.αbar * M.v i - M.l i) := by
        field_simp; ring
      simp only [hg, surpH, surpL, payU, payD, hyb_z i h, hfrac]
      linear_combination (-2 * zt M i * M.l i) * hk
    have hS2 : ∀ i ∈ Finset.univ \ S, g i = x * (M.pH i * M.v i) + (1 - x) * (M.p0 i * M.v i) := by
      intro i hi
      have h : ¬ IsHybrid M β x i := fun h' => (Finset.mem_sdiff.mp hi).2 ((hmem i).mpr h')
      simp only [hg, surpH, surpL, payU, payD, non_z i h, non_y i h]
      ring
    rw [Finset.sum_congr rfl hS1, Finset.sum_congr rfl hS2, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  unfold welfare
  rw [hW, hR, add_comm (∑ i ∈ S, g i), Finset.sum_sdiff (Finset.subset_univ S)]
