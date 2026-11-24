-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.cob_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:06:16.722828+00:00
-- url     : https://prove2.me/submissions/5746191b-9927-4dc7-a838-6bc8d40ebfca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
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
private theorem mvSubst_add_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f + g) = subst φ f + subst φ g := by
  first
  | exact MvPowerSeries.subst_add hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_add _ f g)
  | exact map_add (substAlgHom hφ) f g
private theorem powerSeries_subst_add_of_constantCoeff_eq_zero {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f g : PowerSeries K) :
    PowerSeries.subst a (f + g) = PowerSeries.subst a f + PowerSeries.subst a g := by
  show subst (fun _ : Unit => a) (f + g) = subst (fun _ : Unit => a) f + subst (fun _ : Unit => a) g
  exact mvSubst_add_of_hasSubst (hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha) f g
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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) (f g : PowerSeries K) :
    cob F (f + g) = cob F f + cob F g := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold cob at1
  rw [powerSeries_subst_add_of_constantCoeff_eq_zero hF0, powerSeries_subst_add_of_constantCoeff_eq_zero (hX 0), powerSeries_subst_add_of_constantCoeff_eq_zero (hX 1)]
  ring
end Formalism.L2.Th1.D.TraceNormBounds
