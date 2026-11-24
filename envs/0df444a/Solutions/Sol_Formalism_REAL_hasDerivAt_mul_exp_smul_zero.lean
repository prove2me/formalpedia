-- Prove2me | solution 1 for Formalism.REAL.hasDerivAt_mul_exp_smul_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:08.492505+00:00
-- url     : https://prove2.me/submissions/1756d573-685b-41ce-a5b3-8d279f7ff49f

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Theorems.Thm_Formalism_REAL_tendsto_slope_mul_exp_smul

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  hasDerivAt_iff_tendsto_slope.mpr (tendsto_slope_mul_exp_smul g X)
end Formalism.REAL
