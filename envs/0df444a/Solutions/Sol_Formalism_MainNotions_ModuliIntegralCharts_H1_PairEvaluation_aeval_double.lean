-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.aeval_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:59.424887+00:00
-- url     : https://prove2.me/submissions/9862e482-d6ad-43a1-98fa-fe1b25650b4d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable {σ τ : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
theorem _root_.solution {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j) :
    aeval (fun i => X i + X i) h = C ((2 : S) ^ j) * h := by
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = j := by
    have := hh (mem_support_iff.1 he)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have h2 : ∀ i (k : ℕ), (X i + X i : MvPolynomial σ S) ^ k = C 2 ^ k * X i ^ k := by
    intro i k; rw [← two_mul, mul_pow, ← map_ofNat C 2]
  have key : e.prod (fun i k => (X i + X i : MvPolynomial σ S) ^ k) =
      C ((2 : S) ^ e.degree) * e.prod (fun i k => (X i : MvPolynomial σ S) ^ k) := by
    unfold Finsupp.prod
    simp_rw [h2]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]
    rfl
  rw [aeval_monomial, monomial_eq, key, ← hdeg, algebraMap_eq]
  ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
