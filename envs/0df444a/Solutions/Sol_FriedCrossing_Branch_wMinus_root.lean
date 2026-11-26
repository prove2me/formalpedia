-- Prove2me | solution 1 for FriedCrossing.Branch.wMinus_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:02:43.477549+00:00
-- url     : https://prove2.me/submissions/36a59e29-d9e5-4d68-9d0e-a3875c1db214

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Branch
open TwinRate PureZeros
namespace FriedCrossing.Branch
theorem _root_.solution {a b : ℝ} (hD : 0 ≤ disc a b) : wMinus a b ^ 2 - a * wMinus a b + b = 0 := by
  have h := Real.sq_sqrt hD
  unfold disc at h; unfold wMinus disc; linear_combination h / 4
end FriedCrossing.Branch
