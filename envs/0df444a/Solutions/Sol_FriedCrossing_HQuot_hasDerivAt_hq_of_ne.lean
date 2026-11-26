-- Prove2me | solution 1 for FriedCrossing.HQuot.hasDerivAt_hq_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:23.721462+00:00
-- url     : https://prove2.me/submissions/57d956f0-da3f-4d8e-9685-782f7f5bbbc3

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot
namespace FriedCrossing.HQuot
theorem _root_.solution {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : HasDerivAt (hq f f') (hq' f f' f'' τ) τ := by
  have h : HasDerivAt (fun t => (f t - f 0) / t) ((f' τ * τ - (f τ - f 0) * 1) / τ ^ 2) τ :=
    ((hf τ).sub_const (f 0)).div (hasDerivAt_id' τ) hτ
  have heq : hq f f' =ᶠ[𝓝 τ] fun t => (f t - f 0) / t := by
    filter_upwards [eventually_ne_nhds hτ] with t ht
    simp [hq, ht]
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [hq', hτ, if_false]; ring
end FriedCrossing.HQuot
