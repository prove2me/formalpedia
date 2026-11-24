-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.swap_variables_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:53.683975+00:00
-- url     : https://prove2.me/submissions/3320d92f-549f-4f23-a1d6-fa0fcdfef17e

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
private theorem hasSubst_vec_pair_of_constantCoeff_eq_zero {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_finite_of_constantCoeff_eq_zero fun i => by fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]
private theorem mvSubst_add_of_hasSubst {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f + g) = subst φ f + subst φ g := by
  first
  | exact MvPowerSeries.subst_add hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_add _ f g)
  | exact map_add (substAlgHom hφ) f g
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
theorem _root_.solution (H H' : MvPowerSeries (Fin 2) K) : swap2 (H + H') = swap2 H + swap2 H' := by
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold swap2
  exact mvSubst_add_of_hasSubst (hasSubst_vec_pair_of_constantCoeff_eq_zero (hX 1) (hX 0)) H H'
end Formalism.L2.Th1.D.TraceNormBounds
