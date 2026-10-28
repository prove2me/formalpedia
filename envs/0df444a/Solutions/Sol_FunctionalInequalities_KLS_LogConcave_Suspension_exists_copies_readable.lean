-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:51.158244+00:00
-- url     : https://prove2.me/submissions/93b2e901-f279-466c-8236-7993c1e9dc79

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic

noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A positive finite number of copies satisfies (110) for any positive curvature and finite
nonnegative Hessian bound. -/
theorem solution {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 ≤ beta) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((beta * M / a) ^ 2 + 1)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by nlinarith [sq_nonneg (beta * M / a)]
    exact_mod_cast this
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hratio : 0 ≤ beta * M / a := div_nonneg (mul_nonneg hbeta hM) ha.le
  have hsmall : beta * M / a ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hmul : beta * M ≤ a * Real.sqrt (N : ℝ) := by
    have := (div_le_iff₀ ha).1 hsmall
    nlinarith
  refine ⟨N, hNpos, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hspos]
  exact hmul
