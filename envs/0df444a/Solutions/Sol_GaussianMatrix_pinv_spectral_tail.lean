-- Prove2me | solution 1 for GaussianMatrix.pinv_spectral_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:44:55.192907+00:00
-- url     : https://prove2.me/submissions/5dd48028-f0c9-4dca-89a9-718b4b3b5f42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_wishart_lambda_min_tail
import Theorems.Thm_GaussianMatrix_specNorm_inv_gram_eq
import Theorems.Thm_GaussianMatrix_specNorm_pinvR_sq

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- The scalar inequality behind the Stirling simplification: for an integer `N ≥ 1`,
`(1/Γ(N+1)) ((K+R)/(2t²))^{N/2} ≤ (2πN)^{-1/2} (e√K/N)^N t^{-N}` when `0 ≤ R ≤ K`. -/
lemma pst_real {N : ℕ} (hN : 1 ≤ N) (K R t : ℝ) (hRK : R ≤ K) (hR : 0 ≤ R) (ht : 0 < t) :
    (1 / Real.Gamma ((N : ℝ) + 1)) * (1 / t ^ 2 * (K + R) / 2) ^ ((N : ℝ) / 2)
      ≤ (1 / Real.sqrt (2 * Real.pi * N)) * (Real.exp 1 * Real.sqrt K / N) ^ (N : ℝ)
          * t ^ (-(N : ℝ)) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK : 0 ≤ K := le_trans hR hRK
  rw [Real.Gamma_nat_eq_factorial]
  have hst := Stirling.le_factorial_stirling N
  have hS0 : 0 < Real.sqrt (2 * Real.pi * N) * (N / Real.exp 1) ^ N := by
    have : 0 < 2 * Real.pi * N := by positivity
    positivity
  set y : ℝ := 1 / t ^ 2 * (K + R) / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hy : y ^ ((N : ℝ) / 2) = (Real.sqrt y) ^ N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy0]
    ring_nf
  have hsy : Real.sqrt y = Real.sqrt ((K + R) / 2) / t := by
    rw [show y = ((K + R) / 2) / t ^ 2 by rw [hy_def]; ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq ht.le]
  have hle : Real.sqrt ((K + R) / 2) ≤ Real.sqrt K := Real.sqrt_le_sqrt (by linarith)
  rw [hy, hsy, Real.rpow_natCast, Real.rpow_neg ht.le, Real.rpow_natCast]
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  calc 1 / (N.factorial : ℝ) * (Real.sqrt ((K + R) / 2) / t) ^ N
      ≤ 1 / (N.factorial : ℝ) * (Real.sqrt K / t) ^ N := by
        gcongr
    _ ≤ 1 / (Real.sqrt (2 * Real.pi * N) * (N / Real.exp 1) ^ N) * (Real.sqrt K / t) ^ N := by
        gcongr
    _ = 1 / Real.sqrt (2 * Real.pi * N) * (Real.exp 1 * Real.sqrt K / N) ^ N * (t ^ N)⁻¹ := by
        have h1 : Real.sqrt (2 * Real.pi * N) ≠ 0 := by
          have : 0 < 2 * Real.pi * N := by positivity
          positivity
        have h2 : (N : ℝ) ≠ 0 := by positivity
        simp only [div_pow, mul_pow]
        field_simp

open scoped Matrix.Norms.L2Operator in
lemma pst_specNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : 0 ≤ specNorm A := norm_nonneg _

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | t < specNorm (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * ((k : ℝ) - r + 1)))
          * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r + 1)) ^ ((k : ℝ) - r + 1)
          * t ^ (-((k : ℝ) - r + 1))) := by
  have hsub : {G : Fin r → Fin k → ℝ | t < specNorm (pinvR (Matrix.of G))}
      ⊆ {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ 1 / t ^ 2} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    have hP0 : 0 ≤ specNorm (pinvR (Matrix.of G)) := pst_specNorm_nonneg _
    have hsq : specNorm (pinvR (Matrix.of G)) ^ 2 = 1 / sMin (Matrix.of G)ᵀ ^ 2 := by
      rw [specNorm_pinvR_sq, specNorm_inv_gram_eq]
    have h1 : t ^ 2 < 1 / sMin (Matrix.of G)ᵀ ^ 2 := by
      rw [← hsq]; exact pow_lt_pow_left₀ hG ht.le (by norm_num)
    have hs2 : 0 < sMin (Matrix.of G)ᵀ ^ 2 := by
      rcases (sq_nonneg (sMin (Matrix.of G)ᵀ)).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at h1; nlinarith
    have ht2 : 0 < t ^ 2 := by positivity
    rw [lt_div_iff₀ hs2] at h1
    rw [le_div_iff₀ ht2]
    linarith
  refine (measure_mono hsub).trans ?_
  have hr1 : 1 ≤ r := by omega
  refine (wishart_lambda_min_tail hr1 hrk (1 / t ^ 2) (by positivity)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  set N : ℕ := k - r + 1 with hN_def
  have hN : (N : ℝ) = (k : ℝ) - r + 1 := by
    rw [hN_def, Nat.cast_add, Nat.cast_sub hrk]; push_cast; ring
  have hN2 : (k : ℝ) - r + 2 = (N : ℝ) + 1 := by rw [hN]; ring
  rw [hN2, ← hN]
  have hRK : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have := pst_real (N := N) (by omega) (k : ℝ) (r : ℝ) t hRK (by positivity) ht
  convert this using 3
