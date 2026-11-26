-- Prove2me | solution 1 for FriedCrossing.Regularity.differentiable_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:41:14.604721+00:00
-- url     : https://prove2.me/submissions/53408345-c06f-4e95-8112-7fd74dcbb80e

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2 :=
  (hf.of_le (le_trans le_add_self hmn)).differentiable one_ne_zero
end FriedCrossing.Regularity
