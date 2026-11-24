-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.theorem_s_from_k_one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:46:25.307665+00:00
-- url     : https://prove2.me/submissions/0031cee8-0d54-488d-a2c2-eda4ab953419

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_Gtot
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h : ThmSCore) (hs : SimeqRules) : CyclicPowerClassOfExpEquiv := by
  intro K _ _ _ p ν r0 r1 _ om oms c c' ϖ μ U0 Φ be hp hn hϖ hO hc hc' hμ0 hμ hU0 hΦ0 hΦ hbe
  obtain ⟨r1', r2, r3, r4, -⟩ := hs K (Bool × EV ν r0 r1)
  obtain ⟨-, -, -, -, r5⟩ := hs K (Fin 2)
  have hsum : ∀ s : Finset (EV ν r0 r1),
      Simeq (∑ e ∈ s, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) be)
        (∑ e ∈ s, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (Gser p c c')) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using r1' 0
    | insert e s he ih =>
      rw [Finset.sum_insert he, Finset.sum_insert he]
      exact r4 _ _ _ _ (r5 _ _ _ _ (fun a => by simp) (fun a => integral_X _) hbe) ih
  have eG : (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) K)) (Gser p c c')) = Gtot p c c' 1 := by
    unfold Gtot
    simp only [map_one, one_mul]
  have h1 : Simeq (Gtot p c c' 1) Φ := by
    rw [← eG]
    exact r2 _ _ (r3 _ _ _ hΦ (hsum Finset.univ))
  obtain ⟨h10, h1I⟩ := h1
  have e : mvExp (-Φ) * U0 = mvExp (-(Gtot (E := EV ν r0 r1) p c c' 1)) *
      (mvExp (Gtot p c c' 1 - Φ) * U0) := by
    rw [← mul_assoc, ← mvExp_add (by rw [map_neg, constantCoeff_Gtot hp.ne_zero, neg_zero]) h10]
    congr 2
    ring
  rw [e]
  exact h K p ν r0 r1 om oms c c' ϖ μ _ hp hn hϖ hO hc hc' hμ0 hμ (integral_mul h1I hU0)
end Formalism.InvariantFactorPaths.G7
