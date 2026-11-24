-- Prove2me | solution 1 for Formalism.L2.Th1.D.second_mean_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:21.693265+00:00
-- url     : https://prove2.me/submissions/fe082061-43fd-4c56-a019-7aadee7bc7bf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_torus_coefficient
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_beMean
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_wt_pow
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_mul_geom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open TorusDerivation
namespace Formalism.L2.Th1.D
theorem _root_.solution : MeanTorusInvariant := by
  intro K _ l d _ σ be0 ι _ om oms ζ hζ
  ext n
  rw [torus_coefficient, coeff_beMean]
  change wt l ζ n * _ = _
  rw [mul_left_comm, ← mul_assoc (wt l ζ n), mul_geom (wt_pow hζ n)]
end Formalism.L2.Th1.D
