-- Prove2me | solution 1 for Formalism.GrowthSums.KapPrime.u5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:38.137929+00:00
-- url     : https://prove2.me/submissions/37a239b3-eb61-4b95-a405-752124f091e9

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
theorem _root_.solution {Cc k N N₁ Q c a Y Z : ℝ} (hk : 1 ≤ k) (hN : 1 ≤ N) (hN₁ : 1 ≤ N₁) (hQ : 1 ≤ Q)
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (hc0 : 0 ≤ c) (hc : c ≤ 2 * Cc * Z)
    (ha : k ^ 3 * N * Q ^ 4 * Z * Y ≤ a) :
    k ^ 3 * N₁ * Q ^ 2 * c / a ≤ 2 * Cc * N₁ / (N * Y) := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by linarith
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hN₁0 : 0 < N₁ := by linarith
  have hW : 0 < k ^ 3 * N * Q ^ 4 * Z * Y := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hW ha
  have hCc : 0 ≤ Cc := by nlinarith
  have hQ2 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  rw [div_le_div_iff₀ ha0 (by positivity)]
  calc k ^ 3 * N₁ * Q ^ 2 * c * (N * Y) ≤ k ^ 3 * N₁ * Q ^ 2 * (2 * Cc * Z) * (N * Y) := by gcongr
    _ = 2 * Cc * N₁ * (k ^ 3 * N * Q ^ 2 * Z * Y) := by ring
    _ ≤ 2 * Cc * N₁ * (k ^ 3 * N * Q ^ 4 * Z * Y) := by gcongr
    _ ≤ 2 * Cc * N₁ * a := by gcongr
end Formalism.GrowthSums.KapPrime
