-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LamModule_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.631199+00:00
-- url     : https://prove2.me/submissions/3a7bd4ba-8433-4da2-8733-96665c2685dc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_one_of_not_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_GlobalTheory_NatCastUnitNorm_norm_natCast_eq_one_of_not_dvd


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
theorem _root_.solution (hD : DworkMv) : LamModule := by
  intro K ι _ _ _ _ p σ hp hpn hσ h N hN hs
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hpn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hr : ‖((N : K))⁻¹‖ = 1 := by
    rw [norm_inv, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hN, inv_one]
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.C ((N : K)⁻¹) * h) = 0 := by
    simp [h0]
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K ι p σ hp hpn hσ _ h0']
  have hc := (hD K ι p σ hp hpn hσ h h0).1 hI
  intro n
  have he : frobVar p (MvPowerSeries.map σ (MvPowerSeries.C ((N : K)⁻¹) * h)) -
      MvPowerSeries.C (p : K) * (MvPowerSeries.C ((N : K)⁻¹) * h) =
      MvPowerSeries.C ((N : K)⁻¹) *
        (frobVar p (MvPowerSeries.map σ h) - MvPowerSeries.C (p : K) * h) := by
    rw [map_mul, MvPowerSeries.map_C, map_inv₀, map_natCast, frobVar_eq_expand hp0,
      frobVar_eq_expand hp0, map_mul, MvPowerSeries.expand_C]
    ring
  rw [he, MvPowerSeries.coeff_C_mul, norm_mul, hr, one_mul]
  exact hc n
end Formalism.InvariantFactorPaths.G7
