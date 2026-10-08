-- Prove2me | solution 1 for CVPricing.CertEquiv.det_coeff_matrix_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:07:29.813808+00:00
-- url     : https://prove2.me/submissions/b39a003d-50a3-42d8-93fe-0b095088126d

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_Model

open CVPricing.CertEquiv in
theorem solution (M : Model) {p₁ p₂ : ℝ} (hp₁ : M.pl ≤ p₁) (h12 : p₁ < p₂)
    (hp₂ : p₂ ≤ M.ph) :
    Matrix.det !![p₂ - 2 * M.ph, 2 * M.ph - p₁; p₁ - M.ph, p₂ - M.ph] =
        (p₂ - 2 * M.ph) * (p₂ - M.ph) + (p₁ - M.ph) * (p₁ - 2 * M.ph) ∧
      0 < (p₂ - 2 * M.ph) * (p₂ - M.ph) + (p₁ - M.ph) * (p₁ - 2 * M.ph) := by
  have hpl := M.pl_pos
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    ring
  · have h1 : 0 ≤ (p₂ - 2 * M.ph) * (p₂ - M.ph) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have h2 : 0 < (p₁ - M.ph) * (p₁ - 2 * M.ph) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
