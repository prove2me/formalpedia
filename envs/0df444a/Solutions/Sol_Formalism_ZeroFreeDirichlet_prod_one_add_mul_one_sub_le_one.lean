-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.prod_one_add_mul_one_sub_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:03.773116+00:00
-- url     : https://prove2.me/submissions/5975f566-0fa1-4ff4-96e9-e0e7bd3dc1e9

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, (1 + 1 / (p : ℝ))) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  · have h2 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    nlinarith
end Formalism.ZeroFreeDirichlet
