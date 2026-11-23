-- Prove2me | solution 1 for Formalism.GrowthSums.KapPrime.u2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:23.073086+00:00
-- url     : https://prove2.me/submissions/a3103b79-163e-4c96-9961-fb319fe55baf

import Mathlib
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_KapPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.GrowthSums
open Formalism.GrowthSums.KapPrime
namespace Formalism.GrowthSums.KapPrime
theorem _root_.solution {k p Y a b' : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hp : k ^ 2 * Y ^ 2 ≤ p) (hb0 : 0 < b')
    (hab : b' ≤ a) : k * b' / (p * a) ≤ 1 / Y := by
  have hY0 : 0 < Y := by linarith
  have hkY : 1 ≤ k * Y := one_le_mul_of_one_le_of_one_le hk hY
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hab
  rw [div_le_div_iff₀ (by positivity) hY0]
  have h1 : k * Y ≤ (k * Y) ^ 2 := le_self_pow₀ hkY (by norm_num)
  have h2 : k * Y ≤ p := by nlinarith
  calc k * b' * Y = (k * Y) * b' := by ring
    _ ≤ p * a := mul_le_mul h2 hab hb0.le hp0.le
    _ = 1 * (p * a) := by ring
end Formalism.GrowthSums.KapPrime
