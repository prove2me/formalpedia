-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.sim_ps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:46.492286+00:00
-- url     : https://prove2.me/submissions/e7f9b12d-2f05-416a-ae1c-db698e42c8b4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_subst0

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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {τ : Type} {g : MvPowerSeries τ K} (hg0 : constantCoeff g = 0) (hg : Integral g)
    {lam : PowerSeries K} (h : Simeq (lam : MvPowerSeries Unit K) 0) :
    Simeq (PowerSeries.subst g lam) 0 := sim_subst0 (φ := fun _ : Unit => g) (fun _ => hg0) (fun _ => hg) h
end Formalism.L2.Th1.D.TraceNormBounds
