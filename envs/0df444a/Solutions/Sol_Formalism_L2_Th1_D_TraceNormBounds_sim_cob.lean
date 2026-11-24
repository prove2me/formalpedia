-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.sim_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:07.491798+00:00
-- url     : https://prove2.me/submissions/52a0105b-bed9-425b-a8fc-4558d5e996e1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_ps
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_simeq_sub_zero_of_simeq_zero
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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) (hF : Integral F)
    {lam : PowerSeries K} (h : Simeq (lam : MvPowerSeries Unit K) 0) : Simeq (cob F lam) 0 := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold cob at1
  exact simeq_sub_zero_of_simeq_zero (simeq_sub_zero_of_simeq_zero (sim_ps hF0 hF h) (sim_ps (hX 0) (integral_X_kummer_theta_logarithms _) h))
    (sim_ps (hX 1) (integral_X_kummer_theta_logarithms _) h)
end Formalism.L2.Th1.D.TraceNormBounds
