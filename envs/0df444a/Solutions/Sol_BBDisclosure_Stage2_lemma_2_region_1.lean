-- Prove2me | solution 1 for BBDisclosure.Stage2.lemma_2_region_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:44:51.754811+00:00
-- url     : https://prove2.me/submissions/10fd7059-e255-4666-83c4-130ccc43e68a

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace Aux_BBD_l2

def D (X z : ℝ) : ℝ := min X (max 0 z)

lemma D_eq (X z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ X) : D X z = z := by
  unfold D; rw [max_eq_right h0, min_eq_right h1]

lemma D_le_max (X z : ℝ) : D X z ≤ max 0 z := min_le_right _ _

lemma D_le_X (X z : ℝ) : D X z ≤ X := min_le_left _ _

lemma idA (X y : ℝ) (hX : 0 ≤ X) : X - min X (max 0 y) = D X (X - y) := by
  unfold D
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma idB1 (x1 y : ℝ) (h : x1 ≤ 1) : min 1 (max x1 y) - x1 = D (1 - x1) (y - x1) := by
  unfold D
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma idB2 (x1 y : ℝ) (h : x1 ≤ 1) : 1 - min 1 (max x1 y) = D (1 - x1) (1 - y) := by
  unfold D
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma br_ok (X K q : ℝ) (hX : 0 < X) (hq : q = K / 2) (hK0 : 0 ≤ K) (hK : K ≤ 4 * X) :
    ∀ p' : ℝ, 0 ≤ p' → p' * D X ((K - p') / 2) ≤ q * D X ((K - q) / 2) := by
  intro p' hp
  subst hq
  rw [D_eq X ((K - K / 2) / 2) (by linarith) (by linarith)]
  have h1 : p' * D X ((K - p') / 2) ≤ p' * max 0 ((K - p') / 2) :=
    mul_le_mul_of_nonneg_left (D_le_max _ _) hp
  rcases le_total ((K - p') / 2) 0 with h | h
  · rw [max_eq_left h] at h1; nlinarith
  · rw [max_eq_right h] at h1; nlinarith [sq_nonneg (2 * p' - K)]

lemma br_char (X K q : ℝ) (hX : 0 < X) (hq : 0 ≤ q)
    (hbr : ∀ p' : ℝ, 0 ≤ p' → p' * D X ((K - p') / 2) ≤ q * D X ((K - q) / 2)) :
    K ≤ 0 ∨ (0 < K ∧ K ≤ 4 * X ∧ q = K / 2) ∨ (4 * X < K ∧ q = K - 2 * X) := by
  have hup : q * D X ((K - q) / 2) ≤ q * max 0 ((K - q) / 2) :=
    mul_le_mul_of_nonneg_left (D_le_max _ _) hq
  have hupX : q * D X ((K - q) / 2) ≤ q * X := mul_le_mul_of_nonneg_left (D_le_X _ _) hq
  rcases le_or_gt K 0 with hK | hK
  · left; exact hK
  right
  rcases le_or_gt K (4 * X) with hK4 | hK4
  · left
    refine ⟨hK, hK4, ?_⟩
    have := hbr (K / 2) (by linarith)
    rw [D_eq X ((K - K / 2) / 2) (by linarith) (by linarith)] at this
    rcases le_total ((K - q) / 2) 0 with h | h
    · rw [max_eq_left h] at hup; nlinarith
    · rw [max_eq_right h] at hup; nlinarith [sq_nonneg (2 * q - K)]
  · right
    refine ⟨hK4, ?_⟩
    have := hbr (K - 2 * X) (by linarith)
    have e : (K - (K - 2 * X)) / 2 = X := by ring
    rw [e, D_eq X X (by linarith) le_rfl] at this
    rcases lt_trichotomy q (K - 2 * X) with h | h | h
    · nlinarith
    · exact h
    · rcases le_total ((K - q) / 2) 0 with h' | h'
      · rw [max_eq_left h'] at hup; nlinarith
      · rw [max_eq_right h'] at hup
        nlinarith [mul_pos (by linarith : 0 < q - (K - 2 * X)) (by linarith : 0 < q - 2 * X)]

end Aux_BBD_l2

open BBDisclosure.Stage2 Aux_BBD_l2 in
theorem solution (x1 uao ubn uan ubo : ℝ)
    (huao : uao ∈ Set.Icc (0 : ℝ) 1) (hubn : ubn ∈ Set.Icc (0 : ℝ) 1)
    (huan : uan ∈ Set.Icc (0 : ℝ) 1) (hubo : ubo ∈ Set.Icc (0 : ℝ) 1)
    (hx : x1 ∈ Set.Ioo (1 / 4 + (uao - ubn) / 4) (3 / 4 + (uan - ubo) / 4)) :
    (∀ p : ℝ × ℝ, IsTurfNashA x1 uao ubn p ↔
      p = ((1 + 2 * x1 + uao - ubn) / 3, (4 * x1 - 1 + ubn - uao) / 3)) ∧
    (∀ p : ℝ × ℝ, IsTurfNashB x1 uan ubo p ↔
      p = ((3 - 4 * x1 + uan - ubo) / 3, (3 - 2 * x1 + ubo - uan) / 3)) := by
  obtain ⟨ha0, ha1⟩ := huao
  obtain ⟨hb0, hb1⟩ := hubn
  obtain ⟨hc0, hc1⟩ := huan
  obtain ⟨hd0, hd1⟩ := hubo
  obtain ⟨hxl, hxu⟩ := hx
  have hx0 : 0 < x1 := by linarith
  have hx1 : x1 < 1 := by linarith
  have hX : 0 < 1 - x1 := by linarith
  have rA : ∀ q pb, revAturfA x1 uao ubn (q, pb) = q * D x1 ((1 + pb + uao - ubn - q) / 2) := by
    intro q pb
    show q * min x1 (max 0 ((1 + pb - q + uao - ubn) / 2)) = _
    rw [show (1 + pb - q + uao - ubn) / 2 = (1 + pb + uao - ubn - q) / 2 by ring]; rfl
  have rB : ∀ pa q, revBturfA x1 uao ubn (pa, q) =
      q * D x1 ((2 * x1 - 1 + pa - uao + ubn - q) / 2) := by
    intro pa q
    show q * (x1 - min x1 (max 0 ((1 + q - pa + uao - ubn) / 2))) = _
    rw [idA _ _ hx0.le, show x1 - (1 + q - pa + uao - ubn) / 2 =
      (2 * x1 - 1 + pa - uao + ubn - q) / 2 by ring]
  have sA : ∀ q pb, revAturfB x1 uan ubo (q, pb) =
      q * D (1 - x1) ((1 + pb + uan - ubo - 2 * x1 - q) / 2) := by
    intro q pb
    show q * (min 1 (max x1 ((1 + pb - q + uan - ubo) / 2)) - x1) = _
    rw [idB1 _ _ hx1.le, show (1 + pb - q + uan - ubo) / 2 - x1 =
      (1 + pb + uan - ubo - 2 * x1 - q) / 2 by ring]
  have sB : ∀ pa q, revBturfB x1 uan ubo (pa, q) =
      q * D (1 - x1) ((1 + pa - uan + ubo - q) / 2) := by
    intro pa q
    show q * (1 - min 1 (max x1 ((1 + q - pa + uan - ubo) / 2))) = _
    rw [idB2 _ _ hx1.le, show 1 - (1 + q - pa + uan - ubo) / 2 =
      (1 + pa - uan + ubo - q) / 2 by ring]
  refine ⟨fun p => ?_, fun p => ?_⟩
  · obtain ⟨pa, pb⟩ := p
    unfold IsTurfNashA
    simp only [rA, rB]
    constructor
    · rintro ⟨h0, h1, hA, hB⟩
      have cA := br_char x1 _ pa hx0 h0 hA
      have cB := br_char x1 _ pb hx0 h1 hB
      rcases cA with cA | ⟨cA1, cA2, cA3⟩ | ⟨cA1, cA2⟩ <;>
        rcases cB with cB | ⟨cB1, cB2, cB3⟩ | ⟨cB1, cB2⟩ <;>
        first
        | (exfalso; linarith)
        | (refine Prod.ext ?_ ?_ <;> dsimp only <;> linarith)
    · intro hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨by linarith, by linarith, ?_, ?_⟩
      · exact br_ok x1 _ _ hx0 (by ring) (by linarith) (by linarith)
      · exact br_ok x1 _ _ hx0 (by ring) (by linarith) (by linarith)
  · obtain ⟨pa, pb⟩ := p
    unfold IsTurfNashB
    simp only [sA, sB]
    constructor
    · rintro ⟨h0, h1, hA, hB⟩
      have cA := br_char (1 - x1) _ pa hX h0 hA
      have cB := br_char (1 - x1) _ pb hX h1 hB
      rcases cA with cA | ⟨cA1, cA2, cA3⟩ | ⟨cA1, cA2⟩ <;>
        rcases cB with cB | ⟨cB1, cB2, cB3⟩ | ⟨cB1, cB2⟩ <;>
        first
        | (exfalso; linarith)
        | (refine Prod.ext ?_ ?_ <;> dsimp only <;> linarith)
    · intro hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨by linarith, by linarith, ?_, ?_⟩
      · exact br_ok (1 - x1) _ _ hX (by ring) (by linarith) (by linarith)
      · exact br_ok (1 - x1) _ _ hX (by ring) (by linarith) (by linarith)
