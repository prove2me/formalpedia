-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.sum_wt_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:02.948889+00:00
-- url     : https://prove2.me/submissions/ea629461-ef4a-4e81-97f5-a017d2c07cae

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution {α : Type*} [Fintype α] (δ : ℝ) :
    ∑ T : Finset α, wt δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by
  have h := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance (R := ℝ) (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, bernsteinPolynomial, nsmul_eq_mul] at h
  have h2 := Finset.sum_powerset_apply_card
    (fun k : ℕ => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * ((k : ℝ) - δ * Fintype.card α) ^ 2)
    (x := (Finset.univ : Finset α))
  rw [Finset.powerset_univ, Finset.card_univ] at h2
  simp only [wt]
  refine h2.trans ?_
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [nsmul_eq_mul]
  ring
end Formalism.RankGapBounds.LocalQuadraticParts
