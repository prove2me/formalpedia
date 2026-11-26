-- Prove2me | solution 1 for FriedCrossing.HQuot.hasDerivAt_hq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:18.507887+00:00
-- url     : https://prove2.me/submissions/3c9df0ad-6b6c-4591-b50a-9c87255c6735

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_HQuot_hasDerivAt_hq_of_ne
import Theorems.Thm_FriedCrossing_HQuot_hasDerivAt_hq_zero

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot
namespace FriedCrossing.HQuot
theorem _root_.solution {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : ContinuousAt f'' 0) (τ : ℝ) :
    HasDerivAt (hq f f') (hq' f f' f'' τ) τ := by
  by_cases hτ : τ = 0
  · subst hτ; exact hasDerivAt_hq_zero hf hf' hc
  · exact hasDerivAt_hq_of_ne hf hτ
end FriedCrossing.HQuot
