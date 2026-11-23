-- Prove2me | solution 1 for Formalism.GrowthSums.KapPrime.u1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:23.088802+00:00
-- url     : https://prove2.me/submissions/9fbabd77-ac35-4b43-a575-182f7d4841ba

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
theorem _root_.solution {k p Y : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hp : k ^ 2 * Y ^ 2 ≤ p) : k / p ^ 2 ≤ 1 / Y := by
  have hY0 : 0 < Y := by linarith
  have hkY : 1 ≤ k * Y := one_le_mul_of_one_le_of_one_le hk hY
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [div_le_div_iff₀ (by positivity) hY0]
  have h1 : k * Y ≤ (k * Y) ^ 4 := le_self_pow₀ hkY (by norm_num)
  have h2 : (k ^ 2 * Y ^ 2) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by positivity) hp 2
  nlinarith
end Formalism.GrowthSums.KapPrime
