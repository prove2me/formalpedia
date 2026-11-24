-- Prove2me | solution 1 for Formalism.L2.LamCM.coeff_aeval_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:13:16.709318+00:00
-- url     : https://prove2.me/submissions/3c744cb1-a0c8-4c0e-929b-58e413916fa4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    coeff μ (aeval (fun w => C (c w) * X w) F) = coeff μ F * ∏ w, c w ^ μ w := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial s a =>
    have hs : (s.prod fun i k => (C (c i) * X i) ^ k : MvPolynomial σ K) = C (∏ w, c w ^ s w) * monomial s 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), map_prod,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [mul_pow, map_pow]
    rw [aeval_monomial, hs, algebraMap_eq, ← mul_assoc, ← C_mul, coeff_C_mul,
      coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_mul]
end Formalism.L2.LamCM
