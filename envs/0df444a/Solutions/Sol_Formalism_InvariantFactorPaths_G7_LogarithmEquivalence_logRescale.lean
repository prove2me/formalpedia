-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.logRescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:01:36.986895+00:00
-- url     : https://prove2.me/submissions/4d631c78-9de2-410a-9eac-e5087df0f277

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_mem_ballRing
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_ps_map_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_right_inv_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_lamF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_one_lamF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_lgF_scale
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_norm_lamF_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_map_altR
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_altR
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_altR
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_charP_quot
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_map_mk_eq_zero_iff

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
theorem _root_.solution : LogRescale := by
  intro K _ _ p ϖ hp hn hϖ
  have hp2 := hp.two_le
  have hsub := norm_lamF_sub hp hn hϖ
  refine ⟨subst_lgF_scale p ϖ, hsub, ?_⟩
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)

  have hint : ∀ n, PowerSeries.coeff n (lamF p ϖ) ∈ ballRing K := by
    intro n
    have e : PowerSeries.coeff n (lamF p ϖ) =
        PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2)) +
          ((if n = 1 then 1 else 0) + (if n = p ^ 2 then 1 else 0)) := by
      rw [map_sub, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      ring
    rw [e]
    refine Subring.add_mem _ (mem_ballRing.2 ((hsub n).trans hp1)) (Subring.add_mem _ ?_ ?_) <;>
      split_ifs <;> first | exact Subring.one_mem _ | exact Subring.zero_mem _
  let l0 : PowerSeries (ballRing K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n (lamF p ϖ), hint n⟩
  have hl0 : PowerSeries.map (ballRing K).subtype l0 = lamF p ϖ := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hc0 : PowerSeries.constantCoeff l0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    refine Subtype.ext ?_
    change PowerSeries.coeff 0 (lamF p ϖ) = 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lamF]
  have hu0 : IsUnit (PowerSeries.coeff 1 l0) := by
    have : PowerSeries.coeff 1 l0 = 1 := by
      rw [PowerSeries.coeff_mk]
      exact Subtype.ext (coeff_one_lamF hp2 ϖ)
    rw [this]
    exact isUnit_one
  have hm0 : PowerSeries.constantCoeff (l0.substInvOfIsUnit hu0) = 0 :=
    PowerSeries.constantCoeff_substInvOfIsUnit l0 hu0
  have hR := PowerSeries.subst_substInvOfIsUnit_right l0 hc0 hu0
  have hL := PowerSeries.subst_substInvOfIsUnit_left l0 hc0 hu0
  have hsm := PowerSeries.HasSubst.of_constantCoeff_zero' hm0
  have hsl := PowerSeries.HasSubst.of_constantCoeff_zero' hc0
  refine ⟨PowerSeries.map (ballRing K).subtype (l0.substInvOfIsUnit hu0), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hm0, map_zero]
  · intro n
    rw [PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (l0.substInvOfIsUnit hu0)).2
  · rw [← hl0, ← ps_map_subst _ hsm, hR, PowerSeries.map_X]
  · rw [← hl0, ← ps_map_subst _ hsl, hL, PowerSeries.map_X]
  ·
    have := charP_quot hp hn
    have e1 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)})) l0 =
        PowerSeries.X + PowerSeries.X ^ (p ^ 2) := by
      have h := (map_mk_eq_zero_iff hp hn (l0 - PowerSeries.X - PowerSeries.X ^ (p ^ 2))).2 (by
        rw [map_sub, map_sub, map_pow, PowerSeries.map_X, hl0]
        exact hsub)
      rw [map_sub, map_sub, map_pow, PowerSeries.map_X] at h
      linear_combination h
    have hL' := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)}))) hL
    rw [ps_map_subst _ hsl, PowerSeries.map_X, e1] at hL'
    have key := right_inv_eq (by simp [hp.ne_zero]) (constantCoeff_altR _ hp2) hL'
      (subst_altR (ballRing K ⧸ Ideal.span {(p : ballRing K)}) hp)
    have h := (map_mk_eq_zero_iff hp hn (l0.substInvOfIsUnit hu0 - altR (ballRing K) p)).1 (by
      rw [map_sub, map_altR, key, sub_self])
    rw [map_sub, map_altR] at h
    exact h
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
