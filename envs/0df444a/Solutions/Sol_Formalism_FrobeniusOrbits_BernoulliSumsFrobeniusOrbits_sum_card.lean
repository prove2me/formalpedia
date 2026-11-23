-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.236288+00:00
-- url     : https://prove2.me/submissions/69ea78e7-4d75-4f78-98e5-a1e93f5d3e64

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames

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
theorem _root_.solution (δ : ℝ) (f : ℕ → ℝ) :
    ∑ T : Finset α, bern δ T * f T.card =
      ∑ k ∈ range (Fintype.card α + 1),
        (bernsteinPolynomial ℝ (Fintype.card α) k).eval δ * f k := by
  have h := Finset.sum_powerset_apply_card
    (fun k => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * f k) (x := (univ : Finset α))
  rw [powerset_univ, card_univ] at h
  simp only [bern]
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  simp [bernsteinPolynomial, nsmul_eq_mul]
  ring
end Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
