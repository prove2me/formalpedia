-- Prove2me | solution 1 for FamousTheorems.ostrowski_rational_function_field_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:18:53.788541+00:00
-- url     : https://prove2.me/submissions/2eefccdd-1e75-492a-83a0-7a78819b1611

import Mathlib

theorem solution {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation (RatFunc K) Γ)
    [v.IsRankOneDiscrete] [Valuation.IsTrivialOn K v] [DecidableEq (RatFunc K)] :
    Xor (v.IsEquiv (RatFunc.inftyValuation K))
      (∃! u : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
        v.IsEquiv (IsDedekindDomain.HeightOneSpectrum.valuation (RatFunc K) u)) :=
  RatFunc.valuation_isEquiv_infty_or_adic
