-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_or_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:27.995464+00:00
-- url     : https://prove2.me/submissions/d5198e42-c9b0-4302-8c36-19f86341aa20

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_le_three_halves
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_four_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_div_le_div_sq_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_log_le_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Kzr_sg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_close_sg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : SizeOr := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOr unitU
  have h1 := F.C0; have h2 := F.CK; have h9 := F.xpos; have h11 := F.Kpos
  have hb := F.b0; have hz := F.zpos; have hz1 := F.z1; have hlx0 := F.lx0; have hlx := F.lxz
  have hr0 := F.rpos
  have hx2 : 1 ≤ P.x ^ 2 := one_le_pow₀ F.x1
  have hp1 : P.x ^ 4 ≤ (P.p₀ : ℝ) - 1 := by linarith [F.px]
  have hx24 : P.x ^ 2 ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hp0 : 0 < (P.p₀ : ℝ) - 1 := by linarith
  have c1 : P.La / P.k ≤ z ^ 2 * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le F.Laz (by positivity) F.kx
  have c2 : 1 / P.K₀ ≤ 1 * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le (le_refl _) (by norm_num) F.x_sq_le_threshold
  have c3 : Real.log P.Xp + Real.log 4 ≤ 3 * z := by
    rw [F.hXp, F.logX]; linarith [F.uz, log_four_le_three_halves]
  have c30 : 0 ≤ Real.log P.Xp + Real.log 4 := by
    rw [F.hXp, F.logX]; linarith [F.u1, log_four_nonneg]
  have c4 : Real.log ((P.p₀ : ℝ) - 1) ≤ z := F.log_le_alt hp0 (by linarith [F.pE])
  have c5 : 2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1) ≤ 4 * z * P.x⁻¹ ^ 2 :=
    F.div_le_div_sq_of_le (by linarith) (by positivity) (by linarith)
  have c12 : 0 ≤ P.La / P.k + 1 / P.K₀ := by
    have := F.La0
    have : 0 < P.k := by linarith [F.kx]
    have : 0 < P.K₀ := by linarith [F.x_sq_le_threshold]
    positivity
  have z3 : z ≤ z ^ 3 := by
    calc z = z ^ 1 := (pow_one z).symm
      _ ≤ z ^ 3 := pow_le_pow_right₀ hz1 (by norm_num)
  have br : (P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
      2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1) ≤ 10 * z ^ 3 * P.x⁻¹ ^ 2 := by
    have d1 : (P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4)
        ≤ (z ^ 2 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (3 * z) := by gcongr
    have d2 : (z ^ 2 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (3 * z) + 4 * z * P.x⁻¹ ^ 2
        = (3 * z ^ 3 + 7 * z) * P.x⁻¹ ^ 2 := by ring
    have d3 : (3 * z ^ 3 + 7 * z) * P.x⁻¹ ^ 2 ≤ (10 * z ^ 3) * P.x⁻¹ ^ 2 := by
      gcongr
      linarith
    linarith
  have key : 2 * P.C * P.lx * P.a * ((P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
      2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1)) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 2 * P.C * P.lx * (P.x * P.b) * ((P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
          2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1))
        ≤ 2 * P.C * P.lx * (P.x * P.b) * (10 * z ^ 3 * P.x⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left br (by positivity)
      _ ≤ 2 * K * z * (P.x * P.b) * (10 * z ^ 3 * P.x⁻¹ ^ 2) := by gcongr
      _ = P.b * (1 / 5 * (P.x * P.x⁻¹)) * (100 * K * z ^ 4 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.Kzr0 4) (F.Kzr_sg (le_refl _))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
