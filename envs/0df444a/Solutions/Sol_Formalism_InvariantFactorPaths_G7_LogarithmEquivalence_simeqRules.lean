-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.simeqRules
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.170201+00:00
-- url     : https://prove2.me/submissions/915aba51-68f0-43c4-b3f9-5654ebcc1874

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mvExp_zero__131a26adf023
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_mvExp__1e315831da0a
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_mvExp__fa9db9cd36a6
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_exp_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


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
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution : SimeqRules := by
  intro K ι _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold Simeq
    rw [sub_self, mvExp_zero']
    exact ⟨map_zero _, integral_one'⟩
  · intro f g h
    unfold Simeq at h ⊢
    have e : g - f = -(f - g) := by ring
    have h0 : MvPowerSeries.constantCoeff (-(f - g)) = 0 := by rw [map_neg, h.1, neg_zero]
    rw [e]
    refine ⟨h0, integral_of_mul_eq_one h.2 (constantCoeff_mvExp' h.1) ?_⟩
    rw [← mvExp_add h0 h.1, neg_add_cancel, mvExp_zero']
  · intro f g h h1 h2
    unfold Simeq at h1 h2 ⊢
    have e : f - h = (f - g) + (g - h) := by ring
    rw [e]
    exact exp_integral_add h1 h2
  · intro f g f' g' h1 h2
    unfold Simeq at h1 h2 ⊢
    have e : f + f' - (g + g') = (f - g) + (f' - g') := by ring
    rw [e]
    exact exp_integral_add h1 h2
  · intro κ _ f g φ h0 hφ h
    unfold Simeq at h ⊢
    have hs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [← MvPowerSeries.subst_sub hs, ← subst_mvExp' hs h.1]
    exact ⟨MvPowerSeries.constantCoeff_subst_eq_zero hs h0 h.1, integral_subst' h0 hφ h.2⟩
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
