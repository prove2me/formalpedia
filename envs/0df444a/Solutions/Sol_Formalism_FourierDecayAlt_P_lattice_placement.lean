-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lattice_placement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:25.048175+00:00
-- url     : https://prove2.me/submissions/961afc80-d066-44a1-85d9-01a1c5b85bb9

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Placement := by
  intro k r m N Del hm hN hmk hk hDel
  have hm' : (m:ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have hmk' : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hk' : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hm2 : (2:ℝ) ≤ m := by linarith
  have hN20 : 20 ≤ N := by rw [hN]; linarith
  have hNk : N ≤ 10 * k := by rw [hN]; linarith
  have hN0 : 0 ≤ N := by linarith
  have hk0 : (0:ℝ) ≤ k := by linarith
  have hk3 : (k:ℝ) ^ 3 ≤ (k:ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hN3 : N ^ 3 ≤ 1000 * (k:ℝ) ^ 3 := by
    have := pow_le_pow_left₀ hN0 hNk 3
    nlinarith
  have hk4 : (256:ℝ) ≤ (k:ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hk' 4; norm_num at this; linarith
  have hN3b : (8000:ℝ) ≤ N ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hN20 3; norm_num at this; linarith
  have hr1 : (r:ℝ) + 1 ≤ k / 2 := by linarith
  have hr1' : 0 ≤ (r:ℝ) + 1 := by linarith
  have hrr : ((r:ℝ) + 1) ^ 2 ≤ (k / 2) ^ 2 := pow_le_pow_left₀ hr1' hr1 2
  refine ⟨by linarith, ?_, by linarith, by linarith, ?_⟩
  · intro j hj
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have : (j:ℝ) * N ^ 2 ≤ (N - 1) * N ^ 2 := mul_le_mul_of_nonneg_right hj (sq_nonneg N)
    nlinarith
  · have t1 : (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 ≤ (k:ℝ) * (10 * k) * (k / 2) ^ 2 := by
      apply mul_le_mul _ hrr (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hNk hk0
    have t2 : N ^ 2 * ((r:ℝ) + 1) ^ 2 ≤ (10 * k) ^ 2 * (k / 2) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hN0 hNk 2) hrr (sq_nonneg _) (by positivity)
    nlinarith
end Formalism.FourierDecayAlt.P
