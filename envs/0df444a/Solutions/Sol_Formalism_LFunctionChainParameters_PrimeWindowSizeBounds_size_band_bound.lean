-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_band_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:58.886911+00:00
-- url     : https://prove2.me/submissions/f1366c4d-ace7-4074-a95d-4c202526e4b4

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_log_two_le_one_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_X1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_div_le_div_sq_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr_sg
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
theorem _root_.solution : SizeBand := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tBand unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hI0 : (0 : ℝ) ≤ P.Ib := Nat.cast_nonneg _
  have hI : (P.Ib : ℝ) ≤ z := F.Ibu.trans F.uz
  have hx24 : P.x ^ 2 ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have c1 : 1 / (P.p₀ : ℝ) ≤ 1 * P.x⁻¹ ^ 2 :=
    F.div_le_div_sq_of_le (le_refl _) (by norm_num) (by linarith [F.px])
  have c10 : 0 ≤ 1 / (P.p₀ : ℝ) := by positivity
  have c2 : P.ρ ≤ P.x⁻¹ ^ 2 := by rw [← F.r2]; exact F.ρx
  have c20 := F.ρ0
  have c3 : Real.log (2 * P.Xp) ≤ 2 * z := by
    rw [F.hXp, Real.log_mul (by norm_num) F.Xpos.ne', F.logX]; linarith [log_two_le_one_alt, F.uz, F.z1]
  have c30 : 0 ≤ Real.log (2 * P.Xp) := by
    rw [F.hXp]; exact Real.log_nonneg (by linarith [F.X1])
  have key : 4 * P.a * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp))) ≤ sg P K * P.b := by
    rw [F.ha]
    calc 4 * (P.x * P.b) * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp)))
        ≤ 4 * (P.x * P.b) * (z * ((4 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (2 * z))) := by gcongr
      _ = P.b * (40 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 2 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 2) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
