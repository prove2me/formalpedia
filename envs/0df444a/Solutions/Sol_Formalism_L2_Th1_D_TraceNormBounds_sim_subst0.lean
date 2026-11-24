-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.sim_subst0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:44.2488+00:00
-- url     : https://prove2.me/submissions/19b3240a-7279-4527-9506-9a4eb56e712e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_zero

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
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
private theorem mvSubst_zero_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) :
    subst φ (0 : MvPowerSeries ι K) = 0 := by
  first
  | exact MvPowerSeries.subst_zero hφ
  | (rw [← coe_substAlgHom hφ]; exact map_zero _)
  | simp
end Alg
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
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
theorem _root_.solution {ι τ : Type} [Finite ι] {f : MvPowerSeries ι K} {φ : ι → MvPowerSeries τ K}
    (h0 : ∀ i, constantCoeff (φ i) = 0) (hi : ∀ i, Integral (φ i)) (h : Simeq f 0) :
    Simeq (subst φ f) 0 := by
  have hS : Formalism.InvariantFactorPaths.G7.SimeqRules := Formalism.InvariantFactorPaths.G7.equivalence_rules
  have h1 := (hS K ι).2.2.2.2 τ f 0 φ h0 hi h
  rwa [mvSubst_zero_of_hasSubst (hasSubst_finite_of_constantCoeff_eq_zero h0)] at h1
end Formalism.L2.Th1.D.TraceNormBounds
