-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.big_cell_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:31.956961+00:00
-- url     : https://prove2.me/submissions/daf3e727-eee0-484b-a96d-3c78e68f809e

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FibreExpansionZeroFails

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.BigCellVanishingThreshold := by
  intro c₃ Cb hc hCb
  refine ⟨c₃ * Cb + 2 * c₃ + 3 * Cb + 4, ?_⟩
  intro r n N o As A₀ hr hn h1 h2 ho hA
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As := by exact_mod_cast h1
  have h2' : (n:ℝ) ^ 3 ≤ As := by exact_mod_cast h2
  have hN : (0:ℝ) ≤ N := by positivity
  have hy : (1:ℝ) ≤ n := by linarith
  have hn2 : (n:ℝ) ^ 2 ≤ As := le_trans (by nlinarith) h2'
  have hn1 : (n:ℝ) ≤ As := le_trans (by nlinarith) hn2
  have hA1 : (1:ℝ) ≤ As := le_trans hy hn1
  have hNn : (N:ℝ) * n ≤ As := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'
  have ho' : (o:ℝ) ≤ Cb * As := by
    calc (o:ℝ) ≤ Cb * N * n := ho
      _ = Cb * (N * n) := by ring
      _ ≤ Cb * As := mul_le_mul_of_nonneg_left hNn hCb
  set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP
  have hAs0 : (0:ℝ) ≤ As := by linarith
  have q2 : ((r:ℝ) + 1) ^ 2 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have q3 : ((r:ℝ) + 1) ^ 3 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have q1 : ((r:ℝ) + 1) ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)

  have p1 : ((r:ℝ) + 1) ^ 2 * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) ^ 2 * o ≤ ((r:ℝ) + 1) ^ 4 * (Cb * As) := mul_le_mul q2 ho' (by positivity) (by positivity)
      _ = Cb * P := by rw [hP]; ring
  have p2 : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ P := by
    have : (r:ℝ) * n ≤ ((r:ℝ) + 1) * As := mul_le_mul (by linarith) hn1 (by positivity) (by positivity)
    calc ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n) ≤ ((r:ℝ) + 1) ^ 2 * (((r:ℝ) + 1) * As) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ((r:ℝ) + 1) ^ 3 * As := by ring
      _ ≤ P := mul_le_mul_of_nonneg_right q3 hAs0
  have p3 : ((r:ℝ) + 1) ^ 2 ≤ P := by
    calc ((r:ℝ) + 1) ^ 2 = ((r:ℝ) + 1) ^ 2 * 1 := by ring
      _ ≤ ((r:ℝ) + 1) ^ 4 * As := mul_le_mul q2 hA1 (by norm_num) (by positivity)
  have p4 : ((r:ℝ) + 1) * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) * o ≤ ((r:ℝ) + 1) ^ 4 * (Cb * As) := mul_le_mul q1 ho' (by positivity) (by positivity)
      _ = Cb * P := by rw [hP]; ring
  have p5 : ((r:ℝ) + 1) ≤ P := by
    calc ((r:ℝ) + 1) = ((r:ℝ) + 1) * 1 := by ring
      _ ≤ ((r:ℝ) + 1) ^ 4 * As := mul_le_mul q1 hA1 (by norm_num) (by positivity)
  have hP0 : 0 ≤ P := by positivity
  have e : c₃ * ((r:ℝ) + 1) ^ 2 * ((o:ℝ) + r * n + 1) =
      c₃ * (((r:ℝ) + 1) ^ 2 * o) + c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n)) + c₃ * ((r:ℝ) + 1) ^ 2 := by ring
  have e' : 3 * ((r:ℝ) + 1) * ((o:ℝ) + 1) = 3 * (((r:ℝ) + 1) * o) + 3 * ((r:ℝ) + 1) := by ring
  rw [e, e']
  have := mul_le_mul_of_nonneg_left p1 hc
  have := mul_le_mul_of_nonneg_left p2 hc
  have := mul_le_mul_of_nonneg_left p3 hc
  nlinarith
end Formalism.FourierDecayAlt.P
