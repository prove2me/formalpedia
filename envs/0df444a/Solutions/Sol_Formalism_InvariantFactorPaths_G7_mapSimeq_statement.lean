-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.mapSimeq_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:42.269636+00:00
-- url     : https://prove2.me/submissions/4f35812e-d322-4f95-a136-2f2f44ff7d78

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open TwoVariableSwapLemmas
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : MapSimeq := by
  intro K0 K ι _ _ _ _ j hj
  refine ⟨?_, ?_⟩
  · rintro f g ⟨h0, hI⟩
    have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.map j f - MvPowerSeries.map j g) = 0 := by
      rw [← map_sub, MvPowerSeries.constantCoeff_map, h0, map_zero]
    refine ⟨h0', ?_⟩
    have hm : MvPowerSeries.map j (mvExp (f - g)) = mvExp (MvPowerSeries.map j (f - g)) := by
      unfold mvExp
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
        PowerSeries.map_exp]
    rw [← map_sub, ← hm]
    intro n
    rw [MvPowerSeries.coeff_map, hj]
    exact hI n
  · intro p c c'
    have hA : MvPowerSeries.map j (Aser K0 p) = Aser K p := by
      ext n
      rw [MvPowerSeries.coeff_map]
      simp only [Aser, MvPowerSeries.coeff_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hA' : MvPowerSeries.map j (Aser' K0 p) = Aser' K p := by
      ext n
      rw [MvPowerSeries.coeff_map]
      simp only [Aser', MvPowerSeries.coeff_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    unfold Gser
    rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C, hA, hA']
end Formalism.InvariantFactorPaths.G7
