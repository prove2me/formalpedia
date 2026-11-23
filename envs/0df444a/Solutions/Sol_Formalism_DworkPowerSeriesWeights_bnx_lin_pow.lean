-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_lin_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:25.98824+00:00
-- url     : https://prove2.me/submissions/e8c2b6f9-bf54-4bb1-8923-f2f10699c6ca

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ)
    (μ : σ →₀ ℕ) :
    coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      ∑ r ∈ Finset.range (k + 1),
        if Finsupp.single x r + Finsupp.single y (k - r) = μ then
          a ^ r * b ^ (k - r) * (k.choose r : K) else 0 := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have e : (C a * X x : MvPowerSeries σ K) ^ r * (C b * X y) ^ (k - r) *
      ((k.choose r : ℕ) : MvPowerSeries σ K) =
      C (a ^ r * b ^ (k - r) * (k.choose r : K)) * (X x ^ r * X y ^ (k - r)) := by
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [e, coeff_C_mul, X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, coeff_monomial]
  by_cases h : Finsupp.single x r + Finsupp.single y (k - r) = μ
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
end Formalism.DworkPowerSeriesWeights
