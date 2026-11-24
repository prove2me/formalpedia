-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_bern
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:22.970732+00:00
-- url     : https://prove2.me/submissions/f6216759-71f1-4156-b708-da7cd77a94d1

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
theorem _root_.solution (δ : ℝ) : ∑ T : Finset α, bern δ T = 1 := by
  have h := sum_card (α := α) δ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]
end Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
