-- Prove2me | solution 1 for CirclePackingConstants.c_n_five
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:46:18.605948+00:00
-- url     : https://prove2.me/submissions/aecace70-7b07-4e83-a95a-131dc14ae8a4

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_r_n_eq_of_sharp_unit_square_separation

noncomputable section

namespace CirclePackingConstants

private def quadrant5 (p : Point) : Bool × Bool :=
  (decide (p.1 ≤ 1 / 2), decide (p.2 ≤ 1 / 2))

private lemma same_half_square {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h : decide (x ≤ 1 / 2) = decide (y ≤ 1 / 2)) :
    (x - y) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
  have hiff : (x ≤ 1 / 2 ↔ y ≤ 1 / 2) := decide_eq_decide.mp h
  by_cases hx : x ≤ 1 / 2
  · have hy := hiff.mp hx
    have h₀ : 0 ≤ 1 / 2 - (x - y) := by linarith
    have h₁ : 0 ≤ 1 / 2 + (x - y) := by linarith
    nlinarith only [mul_nonneg h₀ h₁]
  · have hy : ¬y ≤ 1 / 2 := by
      intro hy
      exact hx (hiff.mpr hy)
    have h₀ : 0 ≤ 1 / 2 - (x - y) := by linarith
    have h₁ : 0 ≤ 1 / 2 + (x - y) := by linarith
    nlinarith only [mul_nonneg h₀ h₁]

private lemma same_quadrant_sqDist_le_half {p q : Point}
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hq : 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1)
    (hcell : quadrant5 p = quadrant5 q) :
    sqDist p q ≤ 1 / 2 := by
  have hxcell : decide (p.1 ≤ 1 / 2) = decide (q.1 ≤ 1 / 2) :=
    congrArg Prod.fst hcell
  have hycell : decide (p.2 ≤ 1 / 2) = decide (q.2 ≤ 1 / 2) :=
    congrArg Prod.snd hcell
  have hx := same_half_square hp.1 hp.2.1 hq.1 hq.2.1 hxcell
  have hy := same_half_square hp.2.2.1 hp.2.2.2 hq.2.2.1 hq.2.2.2 hycell
  unfold sqDist
  nlinarith

private lemma five_points_have_close_pair (p : Fin 5 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) :
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ 1 / 2 := by
  by_contra hclose
  push_neg at hclose
  have hinj : Function.Injective (fun i : Fin 5 ↦ quadrant5 (p i)) := by
    intro i j hcell
    by_contra hij
    exact (not_le_of_gt (hclose i j hij))
      (same_quadrant_sqDist_le_half (hp i) (hp j) hcell)
  have hcard := Fintype.card_le_of_injective _ hinj
  norm_num at hcard

theorem cFiveProof :
    c_n 5 = 5 * Real.pi *
      (((1 / Real.sqrt 2) / (2 * (1 + 1 / Real.sqrt 2)))) ^ 2 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hd_sq : ((1 / Real.sqrt 2 : ℝ) ^ 2) = 1 / 2 := by
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hlower : ∃ p : Fin 5 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) ∧
      ∀ i j, i ≠ j → (1 / Real.sqrt 2 : ℝ) ^ 2 ≤ sqDist (p i) (p j) := by
    refine ⟨![(0, 0), (1, 0), (0, 1), (1, 1), (1 / 2, 1 / 2)], ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i j hij
      rw [hd_sq]
      fin_cases i <;> fin_cases j <;> simp_all [sqDist] <;> norm_num
  have hr := r_n_eq_of_sharp_unit_square_separation
    (n := 5) (d := (1 / Real.sqrt 2 : ℝ))
    (by positivity) hlower (by
      intro p hp
      rcases five_points_have_close_pair p hp with ⟨i, j, hij, hd⟩
      exact ⟨i, j, hij, by simpa [hd_sq] using hd⟩)
  unfold c_n
  rw [hr]
  norm_num

end CirclePackingConstants

theorem solution :
    CirclePackingConstants.c_n 5 = 5 * Real.pi *
      (((1 / Real.sqrt 2) / (2 * (1 + 1 / Real.sqrt 2)))) ^ 2 :=
  CirclePackingConstants.cFiveProof
