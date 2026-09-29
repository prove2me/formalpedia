-- Prove2me | solution 1 for Diaz.rank_one_of_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:43.09852+00:00
-- url     : https://prove2.me/submissions/905c582b-faf2-4f19-a4b7-49bb257a90f1

import Mathlib

open ComplexConjugate

theorem solution {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M.det = 0) :
    ∃ p q : Fin 2 → F, (∀ i j, M i j = p i * q j) ∧
      ∀ w v : Fin 2 → F, ∑ i, ∑ j, w i * M i j * v j
        = (∑ i, w i * p i) * (∑ j, q j * v j) := by
  rw [Matrix.det_fin_two] at hM
  have main : ∃ p q : Fin 2 → F, ∀ i j, M i j = p i * q j := by
    by_cases h00 : M 0 0 = 0
    · by_cases h01 : M 0 1 = 0
      · refine ⟨![0, 1], ![M 1 0, M 1 1], ?_⟩
        intro i j; fin_cases i <;> fin_cases j <;> simp [h00, h01]
      · have h10 : M 1 0 = 0 := by
          have hz : M 0 1 * M 1 0 = 0 := by linear_combination -hM + M 1 1 * h00
          rcases mul_eq_zero.mp hz with hz1 | hz1
          · exact absurd hz1 h01
          · exact hz1
        refine ⟨![M 0 1, M 1 1], ![0, 1], ?_⟩
        intro i j; fin_cases i <;> fin_cases j <;> simp [h00, h10]
    · refine ⟨![M 0 0, M 1 0], ![1, M 0 1 / M 0 0], ?_⟩
      intro i j; fin_cases i <;> fin_cases j <;> simp
      · field_simp
      · field_simp
        linear_combination hM
  obtain ⟨p, q, hpq⟩ := main
  refine ⟨p, q, hpq, ?_⟩
  intro w v
  simp only [Fin.sum_univ_two, hpq]
  ring

/-! ## Stage 2 -/
