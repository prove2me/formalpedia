-- Prove2me | solution 1 for ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:33.334021+00:00
-- url     : https://prove2.me/submissions/9f050fab-1489-4935-9ab8-c6f0aed84356

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hD : x + y - 1 ≠ 0) :
    HasDerivAt (fun s => twoEdgeRatio x s)
      (((1 / y ^ 2 - 1 / x) * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2) y := by
  have hN : HasDerivAt (fun s => 2 - s / x - 1 / s) (1 / y ^ 2 - 1 / x) y := by
    have h := ((hasDerivAt_const y (2 : ℝ)).sub ((hasDerivAt_id y).div_const x)).sub
      ((hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id y) hy.ne')
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hDer : HasDerivAt (fun s => x + s - 1) 1 y := ((hasDerivAt_id y).const_add x).sub_const 1
  have h := hN.div hDer hD
  refine h.congr_deriv ?_
  ring

end
