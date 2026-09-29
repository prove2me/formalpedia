-- Prove2me | solution 1 for DiazModulus.det_linear_forms_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T04:58:27.111287+00:00
-- url     : https://prove2.me/submissions/9b782056-bf40-43a2-b0c0-263e38749fa9

import Mathlib

namespace P14Rel2

/-- Two linear forms in three variables over `ℚ` have a common nonzero zero: the `3 × 3` matrix with
rows the two coefficient vectors and `0` is singular. -/
theorem common_kernel_vec (A : Fin 2 → Fin 2 → Fin 3 → ℚ) :
    ∃ v : Fin 3 → ℚ, v ≠ 0 ∧ (∑ k, A 0 0 k * v k) = 0 ∧ (∑ k, A 0 1 k * v k) = 0 := by
  let N : Matrix (Fin 3) (Fin 3) ℚ := ![A 0 0, A 0 1, 0]
  have hdet : N.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 (fun j => by simp [N])
  obtain ⟨v, hv, hNv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_, ?_⟩
  · have h := congr_fun hNv 0
    simpa [N, Matrix.mulVec, dotProduct] using h
  · have h := congr_fun hNv 1
    simpa [N, Matrix.mulVec, dotProduct] using h

end P14Rel2

/-- Take `v ≠ 0` in the common kernel of `L₀₀` and `L₀₁`; then both products vanish. -/
theorem solution (A : Fin 2 → Fin 2 → Fin 3 → ℚ) :
    ∃ v : Fin 3 → ℚ, v ≠ 0 ∧
      (∑ k, A 0 0 k * v k) * (∑ k, A 1 1 k * v k)
        = (∑ k, A 0 1 k * v k) * (∑ k, A 1 0 k * v k) := by
  obtain ⟨v, hv, h0, h1⟩ := P14Rel2.common_kernel_vec A
  exact ⟨v, hv, by rw [h0, h1, zero_mul, zero_mul]⟩

#print axioms solution
