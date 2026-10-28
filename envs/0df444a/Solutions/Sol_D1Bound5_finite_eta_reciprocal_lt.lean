-- Prove2me | solution 1 for D1Bound5.finite_eta_reciprocal_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:35.821023+00:00
-- url     : https://prove2.me/submissions/8f29326d-d4e7-48c6-be99-fc2cfe3bcc26

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_D1Bound5_finite_eta_power_lower

section
namespace D1Bound5



theorem _root_.solution (T e : ℝ) (hT : 1000 ≤ T) (he : e ≤ 9) :
    1/(1-1/T)^e < (101/100 : ℝ) := by
  have h := finite_eta_power_lower T e hT he
  have hp : 0 < (1-1/T)^e := by linarith only [h]
  exact (div_lt_iff₀ hp).mpr (by linarith only [h])

end D1Bound5
end
