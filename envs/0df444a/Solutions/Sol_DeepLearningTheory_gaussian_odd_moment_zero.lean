-- Prove2me | solution 1 for DeepLearningTheory.gaussian_odd_moment_zero
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T22:04:55.969705+00:00
-- url     : https://prove2.me/submissions/5a7b180e-31b9-4a0c-a8f9-128a742699ac

import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory DeepLearningTheory

theorem solution {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (_hK : K.PosDef)
    (m : ℕ) (μs : Fin (2 * m + 1) → Fin N) :
    gaussExpect K (fun z => ∏ a : Fin (2 * m + 1), z (μs a)) = 0 := by
  have densidade_par (z : Fin N → ℝ) : gaussianDensity K (-z) = gaussianDensity K z := by
    simp [gaussianDensity, gaussQuadForm]
  have produto_impar (z : Fin N → ℝ) :
      (∏ a : Fin (2 * m + 1), (-z) (μs a)) = -(∏ a : Fin (2 * m + 1), z (μs a)) := by
    simp [Finset.prod_neg, (odd_two_mul_add_one m).neg_pow]
  let integrando := fun z => gaussianDensity K z * ∏ a : Fin (2 * m + 1), z (μs a)
  have simetria (z : Fin N → ℝ) : integrando (-z) = -integrando z := by
    change gaussianDensity K (-z) * _ = -(gaussianDensity K z * _)
    rw [densidade_par, produto_impar, mul_neg]
  have troca := integral_neg_eq_self integrando volume
  simp_rw [simetria, integral_neg] at troca
  change (∫ z, integrando z) = 0
  linarith
