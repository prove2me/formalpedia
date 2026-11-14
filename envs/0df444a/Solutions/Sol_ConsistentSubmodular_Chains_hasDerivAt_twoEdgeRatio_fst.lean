-- Prove2me | solution 1 for ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:08.853357+00:00
-- url     : https://prove2.me/submissions/d1b2a4c8-3077-4d52-a075-09754013b793

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {x y : ℝ} (hx : 0 < x) (hD : x + y - 1 ≠ 0) :
    HasDerivAt (fun t => twoEdgeRatio t y)
      ((y / x ^ 2 * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2) x := by
  have hN : HasDerivAt (fun t => 2 - y / t - 1 / y) (y / x ^ 2) x := by
    have h := ((hasDerivAt_const x (2 : ℝ)).sub
      ((hasDerivAt_const x y).div (hasDerivAt_id x) hx.ne')).sub_const (1 / y)
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hDer : HasDerivAt (fun t => t + y - 1) 1 x := ((hasDerivAt_id x).add_const y).sub_const 1
  have h := hN.div hDer hD
  refine h.congr_deriv ?_
  ring

end
