-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.size_discriminant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:58.995938+00:00
-- url     : https://prove2.me/submissions/dcec06ef-fc50-49e1-97a6-a0e23db31457

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_b0
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_rpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xr
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r2
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_zr0
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
theorem _root_.solution : SizeD := by
  intro P e K m T hW hL hm hT
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tD unitU
  have h9 := F.xpos; have hb := F.b0; have hz := F.zpos; have hr0 := F.rpos
  have hx2 : Real.exp 1 ≤ P.x ^ 2 := by
    have a1 := Real.exp_one_lt_d9
    have a2 : (100 : ℝ) ^ 2 ≤ P.x ^ 2 := by
      have := F.hx
      gcongr
    linarith
  have c1 : Real.log P.d / P.d ≤ Real.log (P.x ^ 2) / P.x ^ 2 :=
    Real.log_div_self_antitoneOn (by exact hx2) (by exact hx2.trans F.dx) F.dx
  have c2 : Real.log (P.x ^ 2) / P.x ^ 2 = 2 * P.lx * P.x⁻¹ ^ 2 := by
    rw [Real.log_pow, div_eq_mul_inv, F.r2]; push_cast; rfl
  have hlx := F.lxz
  have key : 2 * P.a * Real.log P.d / P.d ≤ sg P K * P.b := by
    rw [F.ha, mul_div_assoc]
    calc 2 * (P.x * P.b) * (Real.log P.d / P.d)
        ≤ 2 * (P.x * P.b) * (2 * z * P.x⁻¹ ^ 2) := by
          rw [c2] at c1
          have : 2 * P.lx * P.x⁻¹ ^ 2 ≤ 2 * z * P.x⁻¹ ^ 2 := by gcongr
          gcongr
          linarith
      _ = P.b * (4 / 100 * (P.x * P.x⁻¹)) * (100 * z ^ 1 * P.x⁻¹) := by ring
      _ ≤ sg P K * P.b := by
          rw [F.xr]
          exact F.close_sg (by norm_num) (by norm_num) (F.zr0 1) (F.zr_sg (by norm_num))
  have := scale2 hm hT key
  linarith
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
