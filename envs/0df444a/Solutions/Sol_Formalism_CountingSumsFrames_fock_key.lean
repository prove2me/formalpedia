-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:14.758098+00:00
-- url     : https://prove2.me/submissions/545b1a88-6cec-49b4-8f65-fef0bc38072d

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z] (letter : σ → Z)
    (d : Z → ℕ) (α : σ →₀ ℕ)
    (h : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    ∏ z, (d z).factorial =
      factProd α * ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α := by
  classical
  unfold factProd
  rw [← Finset.prod_fiberwise Finset.univ letter (fun i => (α i).factorial), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [Nat.multinomial_spec, h z]
end Formalism.CountingSumsFrames
