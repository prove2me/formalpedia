-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.sim_swap2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:06.109532+00:00
-- url     : https://prove2.me/submissions/503e6908-eace-4b7d-bfcc-d43e221d4b3c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_pair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
namespace TraceNormBounds
section Alg
variable {K : Type} [Field K]
end Alg
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
private theorem integral_X_kummer_theta_logarithms {τ : Type} (x : τ) : Integral (X x : MvPowerSeries τ K) := by
  classical
  unfold Integral
  intro n
  rw [coeff_X]
  split_ifs <;> simp
end Normed
end TraceNormBounds
open TraceNormBounds
end Formalism.L2.Th1.D
end
end

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
theorem _root_.solution {μ : MvPowerSeries (Fin 2) K} (h : Simeq μ 0) : Simeq (swap2 μ) 0 := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold swap2
  exact sim_pair (hX 1) (hX 0) (integral_X_kummer_theta_logarithms _) (integral_X_kummer_theta_logarithms _) h
end Formalism.L2.Th1.D.TraceNormBounds
