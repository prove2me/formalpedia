-- Prove2me | solution 2 for GaussianMatrix.pinv_spectral_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:13:01.400255+00:00
-- url     : https://prove2.me/submissions/0d94e214-6992-4249-b20e-d30174ab6c10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_specNorm_pinvR_sq
import Theorems.Thm_GaussianMatrix_specNorm_inv_gram_eq
import Theorems.Thm_GaussianMatrix_wishart_lambda_min_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

open scoped Matrix.Norms.L2Operator in
theorem solution {r k : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | t < specNorm (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * ((k : ℝ) - r + 1)))
          * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r + 1)) ^ ((k : ℝ) - r + 1)
          * t ^ (-((k : ℝ) - r + 1))) := by
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hsub : {G : Fin r → Fin k → ℝ | t < specNorm (pinvR (Matrix.of G))}
      ⊆ {G : Fin r → Fin k → ℝ | sMin (Matrix.of G)ᵀ ^ 2 ≤ 1 / t ^ 2} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    have hP0 : 0 ≤ specNorm (pinvR (Matrix.of G)) := norm_nonneg _
    have hsq : specNorm (pinvR (Matrix.of G)) ^ 2 = 1 / sMin (Matrix.of G)ᵀ ^ 2 := by
      rw [specNorm_pinvR_sq, specNorm_inv_gram_eq]
    have h1 : t ^ 2 < 1 / sMin (Matrix.of G)ᵀ ^ 2 := by
      rw [← hsq]
      exact pow_lt_pow_left₀ hG ht.le (by norm_num)
    have hs2 : 0 < sMin (Matrix.of G)ᵀ ^ 2 := by
      rcases (sq_nonneg (sMin (Matrix.of G)ᵀ)).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at h1
        nlinarith
    rw [le_div_iff₀ ht2]
    have h1' : t ^ 2 * sMin (Matrix.of G)ᵀ ^ 2 < 1 := by
      rwa [lt_div_iff₀ hs2] at h1
    nlinarith
  refine (measure_mono hsub).trans ?_
  have hr1 : 1 ≤ r := by omega
  have htinv : (0 : ℝ) < 1 / t ^ 2 := by positivity
  set N : ℕ := k - r + 1 with hN_def
  have hN : (N : ℝ) = (k : ℝ) - r + 1 := by
    rw [hN_def, Nat.cast_add, Nat.cast_sub hrk]
    push_cast
    ring
  have hNge : 1 ≤ N := by omega
  have hWish : (gaussianMatrix r k) {G : Fin r → Fin k → ℝ | sMin (Matrix.of G)ᵀ ^ 2 ≤ 1 / t ^ 2}
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((N : ℝ) + 1))
          * ((1 / t ^ 2 * ((k : ℝ) + r) / 2) ^ ((N : ℝ) / 2))) := by
    -- the Tropp--Webber lower tail of the smallest Wishart eigenvalue
    have hwl := wishart_lambda_min_tail hr1 hrk (1 / t ^ 2) (by positivity)
    -- `N = k - r + 1`, so `N + 1 = k - r + 2` and `N / 2 = (k - r + 1) / 2`
    -- rewrite the goal's `N` into the `(k - r + 1)` form used by
    -- `wishart_lambda_min_tail`
    -- `wishart_lambda_min_tail` speaks in terms of `k - r + 1`; re-express
    -- the goal's `N` in those terms.
    have hN1 : (N : ℝ) + 1 = (k : ℝ) - r + 2 := by rw [hN]; ring
    have hN3 : (N : ℝ) / 2 = ((k : ℝ) - r + 1) / 2 := by rw [hN]
    rw [hN1, hN3]
    exact hwl
  have hStirling : (1 / Real.Gamma ((N : ℝ) + 1))
        * ((1 / t ^ 2 * ((k : ℝ) + r) / 2) ^ ((N : ℝ) / 2))
      ≤ (1 / Real.sqrt (2 * Real.pi * N))
        * (Real.exp 1 * Real.sqrt k / N) ^ (N : ℝ) * t ^ (-(N : ℝ)) := by
    rw [Real.Gamma_nat_eq_factorial]
    have hst := Stirling.le_factorial_stirling N
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge
    have hN0 : N ≠ 0 := by omega
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
    have hRK : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
    have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
    have hst' : Real.sqrt (2 * Real.pi * (N : ℝ)) * (((N : ℝ) / Real.exp 1) ^ N)
        ≤ (N.factorial : ℝ) := hst
    set y : ℝ := 1 / t ^ 2 * ((k : ℝ) + r) / 2 with hy_def
    have hy0 : (0 : ℝ) ≤ y := by
      rw [hy_def]
      positivity
    have hy : y ^ ((N : ℝ) / 2) = (Real.sqrt y) ^ N := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy0]
      ring_nf
    have hsy : Real.sqrt y = Real.sqrt (((k : ℝ) + r) / 2) / t := by
      have hy_eq : y = (((k : ℝ) + r) / 2) / t ^ 2 := by rw [hy_def]; ring
      have hK2R : (0 : ℝ) ≤ ((k : ℝ) + r) / 2 := by positivity
      rw [hy_eq, Real.sqrt_div hK2R _, Real.sqrt_sq ht.le]
    have hle : Real.sqrt (((k : ℝ) + r) / 2) ≤ Real.sqrt k := by
      apply Real.sqrt_le_sqrt
      linarith [hRK]
    have hdiv_le : Real.sqrt (((k : ℝ) + r) / 2) / t ≤ Real.sqrt k / t := by
      gcongr
    have hdiv_nonneg : (0 : ℝ) ≤ Real.sqrt (((k : ℝ) + r) / 2) / t :=
      div_nonneg (Real.sqrt_nonneg _) ht.le
    have h2pim : (0 : ℝ) < 2 * Real.pi * (N : ℝ) := by
      apply mul_pos
      apply mul_pos
      · norm_num
      · exact Real.pi_pos
      · exact_mod_cast (by omega : 0 < N)
    have hS0pos : (0 : ℝ) < Real.sqrt (2 * Real.pi * (N : ℝ)) * (((N : ℝ) / Real.exp 1) ^ N) := by
      apply mul_pos (Real.sqrt_pos.mpr h2pim)
      apply pow_pos
      apply div_pos _ (Real.exp_pos 1)
      exact_mod_cast (by omega : 0 < N)
    rw [hy, hsy]
    calc 1 / (N.factorial : ℝ) * ((Real.sqrt (((k : ℝ) + r) / 2) / t)) ^ N
        ≤ 1 / (N.factorial : ℝ) * (Real.sqrt k / t) ^ N := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hdiv_nonneg hdiv_le N
      _ ≤ 1 / (Real.sqrt (2 * Real.pi * (N : ℝ)) * (((N : ℝ) / Real.exp 1) ^ N))
          * ((Real.sqrt k / t) ^ N) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_nonneg (Real.sqrt_nonneg _) ht.le) N)
          exact one_div_le_one_div_of_le hS0pos hst'
      _ = 1 / Real.sqrt (2 * Real.pi * N)
          * (Real.exp 1 * Real.sqrt k / N) ^ (N : ℝ) * t ^ (-(N : ℝ)) := by
          have ht_ne : t ≠ 0 := ne_of_gt ht
          have hsqrt_ne : Real.sqrt (2 * Real.pi * (N : ℝ)) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.mpr h2pim)
          have hexp_ne : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
          have hN0 : N ≠ 0 := by omega
          have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
          rw [Real.rpow_neg ht.le, Real.rpow_natCast, Real.rpow_natCast]
          simp only [div_pow, inv_pow]
          field_simp
          ring_nf
  calc (gaussianMatrix r k) {G : Fin r → Fin k → ℝ | sMin (Matrix.of G)ᵀ ^ 2 ≤ 1 / t ^ 2}
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((N : ℝ) + 1))
          * ((1 / t ^ 2 * ((k : ℝ) + r) / 2) ^ ((N : ℝ) / 2))) := hWish
    _ ≤ ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * ((k : ℝ) - r + 1)))
          * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r + 1)) ^ ((k : ℝ) - r + 1)
          * t ^ (-((k : ℝ) - r + 1))) := by
        rw [← hN]
        exact ENNReal.ofReal_le_ofReal hStirling
