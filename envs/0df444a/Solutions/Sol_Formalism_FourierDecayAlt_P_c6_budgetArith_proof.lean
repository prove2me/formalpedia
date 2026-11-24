-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c6_budgetArith_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:27:03.132949+00:00
-- url     : https://prove2.me/submissions/d2b536f5-fd03-4644-b4ef-bd173ae3bdc3

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
theorem _root_.solution : C6.BudgetArith := by
  intro Cb CV hCb
  refine ⟨Cb ^ 2 + 3 * Cb + 6 * CV + 1, ?_⟩
  intro r n N o κ As A₀ hr hn h1 h2 ho hκ hA
  unfold C6.AV C6.mmV
  push_cast
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have h1' : (N:ℝ) * (n:ℝ) ^ 2 ≤ As := by exact_mod_cast h1
  have h2' : (n:ℝ) ^ 3 ≤ As := by exact_mod_cast h2
  have hV : (0:ℝ) ≤ CV := by positivity
  have hN : (0:ℝ) ≤ N := by positivity
  have hy : (1:ℝ) ≤ n := by linarith
  have hn2 : (n:ℝ) ^ 2 ≤ As := le_trans (by nlinarith) h2'
  have hn1 : (n:ℝ) ≤ As := le_trans (by nlinarith) hn2
  have hR3 : ((r:ℝ) + 1) ^ 3 ≤ As := le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) h2'
  have hr3 : (r:ℝ) ^ 3 ≤ As := le_trans (pow_le_pow_left₀ (by positivity) (by linarith) 3) hR3
  have hNn : (N:ℝ) * n ≤ As := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hN) h1'
  have ho' : (o:ℝ) ≤ Cb * As := by
    calc (o:ℝ) ≤ Cb * N * n := ho
      _ = Cb * (N * n) := by ring
      _ ≤ Cb * As := mul_le_mul_of_nonneg_left hNn hCb
  have hAs0 : (0:ℝ) ≤ As := le_trans (by positivity) hn1
  set P : ℝ := ((r:ℝ) + 1) ^ 4 * As with hP
  have hR4 : (1:ℝ) ≤ ((r:ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hP1 : (As:ℝ) ≤ P := by nlinarith
  have hRR : (r:ℝ) + 1 ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) + 1 = ((r:ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP2 : ((r:ℝ) + 1) * As ≤ P := mul_le_mul_of_nonneg_right hRR hAs0
  have hx4 : (r:ℝ) ^ 4 ≤ ((r:ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hP3 : (r:ℝ) ^ 4 * n ≤ P := mul_le_mul hx4 hn1 (by positivity) (by positivity)
  have hP4 : (r:ℝ) * n ^ 2 ≤ P := mul_le_mul (by linarith) hn2 (by positivity) (by positivity)
  have hx2 : (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 4 := by
    calc (r:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP5 : (r:ℝ) ^ 5 ≤ P := by
    have : (r:ℝ) ^ 5 = (r:ℝ) ^ 2 * (r:ℝ) ^ 3 := by ring
    rw [this]; exact mul_le_mul hx2 hr3 (by positivity) (by positivity)
  have hP6 : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ P := by
    have : ((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ ((r:ℝ) + 1) ^ 3 := by nlinarith
    linarith
  have hκ' : (κ:ℝ) ≤ Cb ^ 2 * P := by
    have a1 : (κ:ℝ) ≤ Cb * ((r:ℝ) + 1) * (Cb * As) :=
      le_trans hκ (mul_le_mul_of_nonneg_left ho' (by positivity))
    have a2 : Cb * ((r:ℝ) + 1) * (Cb * As) = Cb ^ 2 * (((r:ℝ) + 1) * As) := by ring
    rw [a2] at a1
    exact le_trans a1 (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hoR : ((r:ℝ) + 1) * o ≤ Cb * P := by
    calc ((r:ℝ) + 1) * o ≤ ((r:ℝ) + 1) * (Cb * As) := mul_le_mul_of_nonneg_left ho' (by positivity)
      _ = Cb * (((r:ℝ) + 1) * As) := by ring
      _ ≤ Cb * P := mul_le_mul_of_nonneg_left hP2 hCb
  have hP0 : 0 ≤ P := by positivity
  have e1 : (r:ℝ) * (CV * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
      CV * ((r:ℝ) ^ 4 * n) + CV * ((r:ℝ) * n ^ 2) + CV * (r:ℝ) ^ 5 := by ring
  have e2 : 3 * ((r:ℝ) + 1) * (CV * ((r:ℝ) ^ 2 + 1) + o) =
      3 * CV * (((r:ℝ) + 1) * ((r:ℝ) ^ 2 + 1)) + 3 * (((r:ℝ) + 1) * o) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left hP3 hV
  have := mul_le_mul_of_nonneg_left hP4 hV
  have := mul_le_mul_of_nonneg_left hP5 hV
  have := mul_le_mul_of_nonneg_left hP6 (by positivity : (0:ℝ) ≤ 3 * CV)
  nlinarith
end Formalism.FourierDecayAlt.P
