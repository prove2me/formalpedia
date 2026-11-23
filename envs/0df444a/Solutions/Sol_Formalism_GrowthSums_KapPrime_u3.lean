-- Prove2me | solution 1 for Formalism.GrowthSums.KapPrime.u3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:23.0657+00:00
-- url     : https://prove2.me/submissions/be36125a-523f-458e-b91a-8af955ee4a40

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
theorem _root_.solution {k p Y La N₁ : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hN₁ : 1 ≤ N₁) (hp : k ^ 2 * Y ^ 2 ≤ p)
    (_hLa0 : 0 ≤ La) (hLa : La < k) : La * N₁ / p ≤ N₁ / Y := by
  have hY0 : 0 < Y := by linarith
  have hkY : 1 ≤ k * Y := one_le_mul_of_one_le_of_one_le hk hY
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [div_le_div_iff₀ hp0 hY0]
  have h1 : k * Y ≤ (k * Y) ^ 2 := le_self_pow₀ hkY (by norm_num)
  have h2 : La * Y ≤ p := by nlinarith
  have hN₁0 : 0 ≤ N₁ := by linarith
  calc La * N₁ * Y = N₁ * (La * Y) := by ring
    _ ≤ N₁ * p := mul_le_mul_of_nonneg_left h2 hN₁0
end Formalism.GrowthSums.KapPrime
