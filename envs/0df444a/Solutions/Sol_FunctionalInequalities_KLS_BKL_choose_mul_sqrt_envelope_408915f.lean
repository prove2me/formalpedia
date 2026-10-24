-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:17:43.420996+00:00
-- url     : https://prove2.me/submissions/d8577972-ef52-460d-8257-9a0721f277dd

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities.KLS.BKL in
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
