-- Prove2me | solution 1 for Formalism.GrowthSums.KapPrime.u4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:23.109963+00:00
-- url     : https://prove2.me/submissions/4ffcf975-cb51-4786-83cb-19041ae1ec6b

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
theorem _root_.solution {k Y Yb N La la a b' : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hYb : 1 ≤ Yb) (hN : 1 ≤ N)
    (hla : 1 ≤ la) (hLa : 1 ≤ La) (hb0 : 0 < b') (ha : k * Y ^ 2 * Yb * N * La * la * b' ≤ a) :
    La * b' / a ≤ 1 / Y := by
  have hY0 : 0 < Y := by linarith
  have hm : 1 ≤ k * Y * Yb * N * la :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk hY) hYb) hN) hla
  have hLa0 : 0 < La := by linarith
  have hLb : 0 ≤ La * b' * Y := by positivity
  have h1 : La * b' * Y * 1 ≤ La * b' * Y * (k * Y * Yb * N * la) :=
    mul_le_mul_of_nonneg_left hm hLb
  have ha0 : 0 < a := by
    have : 0 < k * Y ^ 2 * Yb * N * La * la * b' := by
      have : 0 < k := by linarith
      have : 0 < Yb := by linarith
      have : 0 < N := by linarith
      have : 0 < la := by linarith
      positivity
    linarith
  rw [div_le_div_iff₀ ha0 hY0]
  have h2 : La * b' * Y * (k * Y * Yb * N * la) = k * Y ^ 2 * Yb * N * La * la * b' := by ring
  linarith
end Formalism.GrowthSums.KapPrime
