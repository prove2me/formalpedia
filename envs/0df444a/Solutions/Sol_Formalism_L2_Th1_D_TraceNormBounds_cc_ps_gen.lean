-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.cc_ps_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:38.940977+00:00
-- url     : https://prove2.me/submissions/d6e38cc8-0873-452f-9cdf-14d984d02f1b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_ps


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
theorem _root_.solution {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f : PowerSeries K) : constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have e : f = PowerSeries.C (PowerSeries.constantCoeff f) +
      (f - PowerSeries.C (PowerSeries.constantCoeff f)) := by ring
  conv_lhs => rw [e]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add, Pair.cc_ps ha (by simp), add_zero,
    constantCoeff_C]
end Formalism.L2.Th1.D.TraceNormBounds
