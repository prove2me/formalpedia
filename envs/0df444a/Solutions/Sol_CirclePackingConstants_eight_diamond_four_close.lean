-- Prove2me | solution 1 for CirclePackingConstants.eight_diamond_four_close
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T06:40:43.634885+00:00
-- url     : https://prove2.me/submissions/dbfc5a58-5534-4490-885d-7ab6619106ed

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem cyc_aux (ρ a1 a2 a3 a4 : ℝ) (h1 : 0 ≤ a1) (h1' : a1 ≤ ρ) (h2 : a2 ≤ 0) (h2' : -ρ ≤ a2)
    (h3 : a3 ≤ 0) (h3' : -ρ ≤ a3) (h4 : 0 ≤ a4) (h4' : a4 ≤ ρ) :
    (a1 - a2)^2 + (a2 - a3)^2 + (a3 - a4)^2 + (a4 - a1)^2 ≤ 8 * ρ^2 := by
  nlinarith [mul_nonneg h1 (sub_nonneg.2 h1'), mul_nonneg (neg_nonneg.2 h2) (by linarith : 0 ≤ a2 + ρ),
    mul_nonneg (neg_nonneg.2 h3) (by linarith : 0 ≤ a3 + ρ), mul_nonneg h4 (sub_nonneg.2 h4'),
    mul_nonneg h1 (neg_nonneg.2 h2), mul_nonneg h1 (neg_nonneg.2 h3), mul_nonneg h4 (neg_nonneg.2 h2),
    mul_nonneg h4 (neg_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h1') (sub_nonneg.2 h4'),
    mul_nonneg (by linarith : 0 ≤ a2 + ρ) (by linarith : 0 ≤ a3 + ρ),
    mul_nonneg (sub_nonneg.2 h1') (by linarith : 0 ≤ a2 + ρ), mul_nonneg (sub_nonneg.2 h4') (by linarith : 0 ≤ a3 + ρ),
    mul_nonneg (sub_nonneg.2 h1') (by linarith : 0 ≤ a3 + ρ), mul_nonneg (sub_nonneg.2 h4') (by linarith : 0 ≤ a2 + ρ)]


noncomputable def quadIdx (P Q : Fin 4 → ℝ) (i : Fin 4) : Fin 4 :=
  if 0 ≤ P i then (if 0 ≤ Q i then 0 else 3) else (if 0 ≤ Q i then 1 else 2)

theorem quadIdx_spec (P Q : Fin 4 → ℝ) (i : Fin 4) :
    (quadIdx P Q i = 0 → 0 ≤ P i ∧ 0 ≤ Q i) ∧ (quadIdx P Q i = 1 → P i ≤ 0 ∧ 0 ≤ Q i) ∧
    (quadIdx P Q i = 2 → P i ≤ 0 ∧ Q i ≤ 0) ∧ (quadIdx P Q i = 3 → 0 ≤ P i ∧ Q i ≤ 0) := by
  unfold quadIdx
  split_ifs with h1 h2 h2 <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first | (exfalso; revert h; decide) | exact ⟨by linarith, by linarith⟩

theorem four_in_square_rot (ρ : ℝ) (hρ : 0 ≤ ρ) (P Q : Fin 4 → ℝ)
    (hP : ∀ i, |P i| ≤ ρ) (hQ : ∀ i, |Q i| ≤ ρ) :
    ∃ i j : Fin 4, i ≠ j ∧ (P i - P j)^2 + (Q i - Q j)^2 ≤ 4 * ρ^2 := by
  by_contra hcon
  push Not at hcon
  have hP' : ∀ i, -ρ ≤ P i ∧ P i ≤ ρ := fun i => abs_le.mp (hP i)
  have hQ' : ∀ i, -ρ ≤ Q i ∧ Q i ≤ ρ := fun i => abs_le.mp (hQ i)
  -- same quadrant ⇒ close
  have hsame : ∀ i j, i ≠ j → quadIdx P Q i ≠ quadIdx P Q j := by
    intro i j hij hq
    have := hcon i j hij
    have si := quadIdx_spec P Q i
    have sj := quadIdx_spec P Q j
    have pi := hP' i; have pj := hP' j; have qi := hQ' i; have qj := hQ' j
    generalize hk : quadIdx P Q i = k at *
    rw [← hq] at sj
    fin_cases k <;> simp at si sj <;> nlinarith [mul_nonneg hρ hρ]
  have hinj : Function.Injective (quadIdx P Q) := fun i j h => by
    by_contra hne; exact hsame i j hne h
  have hsurj := Finite.injective_iff_surjective.mp hinj
  obtain ⟨w0, hw0⟩ := hsurj 0
  obtain ⟨w1, hw1⟩ := hsurj 1
  obtain ⟨w2, hw2⟩ := hsurj 2
  obtain ⟨w3, hw3⟩ := hsurj 3
  have s0 := (quadIdx_spec P Q w0).1 hw0
  have s1 := (quadIdx_spec P Q w1).2.1 hw1
  have s2 := (quadIdx_spec P Q w2).2.2.1 hw2
  have s3 := (quadIdx_spec P Q w3).2.2.2 hw3
  have ne : ∀ i j, quadIdx P Q i ≠ quadIdx P Q j → i ≠ j := fun i j h e => h (e ▸ rfl)
  have h01 := hcon w0 w1 (ne _ _ (by rw [hw0, hw1]; decide))
  have h12 := hcon w1 w2 (ne _ _ (by rw [hw1, hw2]; decide))
  have h23 := hcon w2 w3 (ne _ _ (by rw [hw2, hw3]; decide))
  have h30 := hcon w3 w0 (ne _ _ (by rw [hw3, hw0]; decide))
  have cx := cyc_aux ρ (P w0) (P w1) (P w2) (P w3) s0.1 (hP' _).2 s1.1 (hP' _).1 s2.1 (hP' _).1 s3.1 (hP' _).2
  have cy := cyc_aux ρ (Q w1) (Q w2) (Q w3) (Q w0) s1.2 (hQ' _).2 (s2.2) (hQ' _).1 s3.2 (hQ' _).1 s0.2 (hQ' _).2
  nlinarith

theorem diamond_four_core : ∀ p : Fin 4 → Point,
    (∀ i, |(p i).1 - 1 / 2| + |(p i).2 - 1 / 2| ≤ (Real.sqrt 3 - 1) / 2) →
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ 2 - Real.sqrt 3 := by
  intro p hp
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 1 ≤ Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set ρ : ℝ := (Real.sqrt 3 - 1) / 2 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  obtain ⟨i, j, hij, h⟩ := four_in_square_rot ρ hρ0
    (fun i => ((p i).1 - 1 / 2) + ((p i).2 - 1 / 2)) (fun i => ((p i).1 - 1 / 2) - ((p i).2 - 1 / 2))
    (fun i => (abs_add_le _ _).trans (hp i)) (fun i => (abs_sub _ _).trans (hp i))
  refine ⟨i, j, hij, ?_⟩
  unfold sqDist
  have : 2 * ρ ^ 2 = 2 - Real.sqrt 3 := by rw [hρ]; nlinarith
  nlinarith

end CirclePackingConstants

open CirclePackingConstants in
theorem solution : ∀ p : Fin 4 → Point,
    (∀ i, |(p i).1 - 1 / 2| + |(p i).2 - 1 / 2| ≤ (Real.sqrt 3 - 1) / 2) →
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ 2 - Real.sqrt 3 := diamond_four_core
