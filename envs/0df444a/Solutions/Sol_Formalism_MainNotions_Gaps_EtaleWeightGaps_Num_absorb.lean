-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.absorb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:36.549145+00:00
-- url     : https://prove2.me/submissions/37c93e4f-846f-4e79-8d13-94b41fc898b1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
theorem _root_.solution {k b c : ℝ} (hk : 1 ≤ k) (hb : 10 ^ 100 ≤ b) (hc0 : 0 ≤ c) (hc : c ≤ 10 ^ 100) {i j : ℕ} (hi : i ≤ 8)
    (hj : j + 1 ≤ 8) : c * k ^ i * b ^ j ≤ (k * b) ^ 8 := by
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) hb
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hki : k ^ i ≤ k ^ 8 := pow_le_pow_right₀ hk hi
  have hbj : b ^ j ≤ b ^ 7 := pow_le_pow_right₀ hb1 (by omega)
  have s1 : c * k ^ i ≤ 10 ^ 100 * k ^ 8 := mul_le_mul hc hki (pow_nonneg hk0 i) (by norm_num)
  have s2 : c * k ^ i * b ^ j ≤ 10 ^ 100 * k ^ 8 * b ^ 7 :=
    mul_le_mul s1 hbj (pow_nonneg hb0 j) (mul_nonneg (by norm_num) (pow_nonneg hk0 8))
  have s3 : 10 ^ 100 * k ^ 8 * b ^ 7 ≤ b * k ^ 8 * b ^ 7 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (pow_nonneg hk0 8)) (pow_nonneg hb0 7)
  calc c * k ^ i * b ^ j ≤ b * k ^ 8 * b ^ 7 := le_trans s2 s3
    _ = (k * b) ^ 8 := by ring
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
