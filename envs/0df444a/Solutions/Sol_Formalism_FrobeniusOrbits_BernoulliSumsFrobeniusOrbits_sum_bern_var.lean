-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_bern_var
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.674445+00:00
-- url     : https://prove2.me/submissions/394c3584-30a5-4744-92b2-6e419bd8ecb0

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames
import Theorems.Thm_Formalism_FrobeniusOrbits_BernoulliSumsFrobeniusOrbits_sum_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
variable {α : Type*} [Fintype α]
namespace Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
theorem _root_.solution (δ : ℝ) :
    ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by
  have h := sum_card (α := α) δ (fun k => ((k : ℝ) - δ * Fintype.card α) ^ 2)
  rw [h]
  have hv := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance ℝ (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, nsmul_eq_mul] at hv
  rw [← hv]
  refine sum_congr rfl fun k _ => ?_
  ring
end Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
