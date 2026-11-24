-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.cc_of_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:17.607406+00:00
-- url     : https://prove2.me/submissions/45ccc6e8-df6c-4e9e-9933-d4d716b17079

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_cc_ps_gen

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {FE : MvPowerSeries (Fin 2) K} (hFE0 : constantCoeff FE = 0)
    {phE : PowerSeries K} (h : constantCoeff (cob FE phE) = 0) :
    PowerSeries.constantCoeff phE = 0 := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold cob at h
  rw [map_sub, map_sub] at h
  unfold at1 at h
  rw [cc_ps_gen hFE0, cc_ps_gen (hX 0), cc_ps_gen (hX 1)] at h
  linear_combination -h
end Formalism.L2.Th1.D.TraceNormBounds
