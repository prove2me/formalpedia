-- Prove2me | solution 1 for Formalism.REAL.tendsto_slope_mul_exp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:50.76893+00:00
-- url     : https://prove2.me/submissions/db0a452b-1777-4df1-893a-1c3c2771f08b

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Theorems.Thm_Formalism_REAL_tendsto_slope_exp_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
  have h := (tendsto_slope_exp_smul X).const_mul g
  refine h.congr (fun t => ?_)
  simp only [slope_def_module, Matrix.mul_sub, Matrix.mul_smul]
end Formalism.REAL
