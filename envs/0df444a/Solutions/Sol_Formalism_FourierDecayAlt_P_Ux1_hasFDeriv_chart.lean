-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.hasFDeriv_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:36.566206+00:00
-- url     : https://prove2.me/submissions/1885ae50-d293-4dc8-8937-a1414f29ccce

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_Lt_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_expandL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_tangent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_aC_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cast_ne_zero
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B4_op_eq_op__514f38137870


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    HasFDerivAt (fun Y' => H (chart g0 Y'))
      (∑ i, (aC g0 i Y).smulRight (op true (Lt i) H (chart g0 Y))) Y := by
  set c := chart g0 Y with hc
  have hcG : c ∈ GV k r := chart_mem hg0 hY
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH c hcG
  have hdiff : DifferentiableAt ℝ h' c :=
    (hcd.differentiableOn (cast_ne_zero 0)).differentiableAt (hU.mem_nhds hcU)
  have hchd := chart_diff g0 hY
  have hcomp : HasFDerivAt (fun Y' => h' (chart g0 Y'))
      ((fderiv ℝ h' c).comp (fderiv ℝ (chart g0) Y)) Y :=
    hdiff.hasFDerivAt.comp Y hchd.hasFDerivAt
  have heq : (fun Y' => H (chart g0 Y')) =ᶠ[𝓝 Y] (fun Y' => h' (chart g0 Y')) := by
    filter_upwards [hchd.continuousAt.preimage_mem_nhds (hU.mem_nhds hcU), dom_open.mem_nhds hY]
      with Y' h1 h2
    exact hff _ h1 (chart_mem hg0 h2)
  refine (hcomp.congr_of_eventuallyEq heq).congr_fderiv ?_
  ext1 W
  rw [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  have hop : ∀ i, op true (Lt i) H c = fderiv ℝ h' c (-(Lt i * c)) := fun i =>
    op_eq_op' 0 true hU hcd hff (Lt_unit i).1 c hcU hcG
  simp_rw [hop, ← map_smul, ← map_sum]
  congr 1
  set Xv := -(fderiv ℝ (chart g0) Y W) * c⁻¹ with hXv
  have hXl : inLie k r Xv := tangent hg0 hY W
  have hA : ∀ i, aC g0 i Y W = kc i Xv := fun i => aC_apply g0 i Y W
  have hXc : Xv * c = -(fderiv ℝ (chart g0) Y W) := by
    rw [hXv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hcu, Matrix.mul_one]
  calc fderiv ℝ (chart g0) Y W = -(Xv * c) := by rw [hXc, neg_neg]
    _ = -((∑ i, kc i Xv • Lt i) * c) := by rw [← expandL hXl]
    _ = ∑ i, aC g0 i Y W • -(Lt i * c) := by
        simp only [hA, Finset.sum_mul, Matrix.smul_mul, smul_neg, Finset.sum_neg_distrib]
end Formalism.FourierDecayAlt.P.Ux1
