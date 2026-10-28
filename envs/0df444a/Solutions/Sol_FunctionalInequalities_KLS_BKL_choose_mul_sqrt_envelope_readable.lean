-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:33:38.408565+00:00
-- url     : https://prove2.me/submissions/bcad4481-7fe8-4a5f-b157-3ad307771cae

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope

noncomputable section
/-- **BKL (105)**: `C(m-1, a-1) √(b_a b_{m-a+1}) = √b_m` for `1 ≤ a ≤ m` (the source uses
`2 ≤ a ≤ m - 2`). -/
theorem solution {K : ℝ} (hK : 0 ≤ K) {m a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) :
    ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K a * FunctionalInequalities.KLS.BKL.envelope K (m - a + 1)) =
      Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) := by
    have hsub : m - a + 1 - 1 = m - a := by
      omega
    have hpow : (a - 1) + (m - a) = m - 1 := by
      omega
    have hfac : ((m - 1).choose (a - 1) : ℝ) *
        ((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ) =
        ((m - 1).factorial : ℝ) := by
      have hchoose := Nat.choose_mul_factorial_mul_factorial
        (n := m - 1) (k := a - 1) (by omega)
      have hsubfac : (m - 1) - (a - 1) = m - a := by
        omega
      rw [hsubfac] at hchoose
      exact_mod_cast hchoose
    have hprod :
        FunctionalInequalities.KLS.BKL.envelope K a * FunctionalInequalities.KLS.BKL.envelope K (m - a + 1) =
          K ^ (m - 1) *
            (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) ^ 2 := by
      simp only [FunctionalInequalities.KLS.BKL.envelope, hsub]
      calc
        K ^ (a - 1) * ((a - 1).factorial : ℝ) ^ 2 *
            (K ^ (m - a) * ((m - a).factorial : ℝ) ^ 2) =
            (K ^ (a - 1) * K ^ (m - a)) *
              (((a - 1).factorial : ℝ) ^ 2 *
                ((m - a).factorial : ℝ) ^ 2) := by ring
        _ = K ^ ((a - 1) + (m - a)) *
              (((a - 1).factorial : ℝ) ^ 2 *
                ((m - a).factorial : ℝ) ^ 2) := by
              rw [pow_add]
        _ = K ^ (m - 1) *
              (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) ^ 2 := by
              rw [hpow]
              ring
    have hsqrtprod :
        Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K a * FunctionalInequalities.KLS.BKL.envelope K (m - a + 1)) =
          Real.sqrt (K ^ (m - 1)) *
            (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) := by
      rw [hprod, Real.sqrt_mul (pow_nonneg hK _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg]
      positivity
    have hsqrtm :
        Real.sqrt (FunctionalInequalities.KLS.BKL.envelope K m) =
          Real.sqrt (K ^ (m - 1)) * ((m - 1).factorial : ℝ) := by
      rw [FunctionalInequalities.KLS.BKL.envelope, Real.sqrt_mul (pow_nonneg hK _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg]
      positivity
    rw [hsqrtprod, hsqrtm]
    calc
      ((m - 1).choose (a - 1) : ℝ) *
          (Real.sqrt (K ^ (m - 1)) *
            (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ))) =
          Real.sqrt (K ^ (m - 1)) *
            (((m - 1).choose (a - 1) : ℝ) *
              ((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) := by
                ring
      _ = Real.sqrt (K ^ (m - 1)) * ((m - 1).factorial : ℝ) := by
        rw [hfac]
