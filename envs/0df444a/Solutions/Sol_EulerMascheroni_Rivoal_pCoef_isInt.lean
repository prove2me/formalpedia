-- Prove2me | solution 1 for EulerMascheroni.Rivoal.pCoef_isInt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:30:36.533483+00:00
-- url     : https://prove2.me/submissions/58634471-bfb8-4868-b79a-492d8a4202a5

import Definitions.Def_eulerMascheroni_rivoalForms
import Theorems.Thm_EulerMascheroni_Rivoal_polyP_newton

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, EulerMascheroni.Rivoal.pCoef n = z := by
  obtain ⟨a, -, -, h⟩ := EulerMascheroni.Rivoal.polyP_newton n hn
  refine ⟨(-1) ^ (n + 1) * ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * a j, ?_⟩
  have hs : (-1 : ℚ) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
    rw [← mul_pow]; norm_num
  push_cast at h ⊢
  rw [h, ← mul_assoc, hs, one_mul]
