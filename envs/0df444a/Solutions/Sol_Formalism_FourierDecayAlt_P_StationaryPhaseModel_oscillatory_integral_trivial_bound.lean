-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.oscillatory_integral_trivial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:37.756278+00:00
-- url     : https://prove2.me/submissions/3fd5501c-024c-4028-9232-d1424fa0c5fc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (r : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (u : (Fin d → ℂ) → ℂ) (hu : ∀ x, ‖u x‖ = 1) (a : (Fin d → ℂ) → V) (S : ℝ)
    (hsupp : Function.support a ⊆ Metric.closedBall 0 r) (hS : ∀ x, ‖a x‖ ≤ S) :
    ‖∫ x : Fin d → ℂ, u x • a x ∂(muPi β (Fin d))‖ ≤
      S * (muPi β (Fin d) (Metric.closedBall 0 r)).toReal := by
  have := isAddHaar_muPi d β hβ
  have h1 : ∫ x : Fin d → ℂ, u x • a x ∂(muPi β (Fin d)) =
      ∫ x in Metric.closedBall (0 : Fin d → ℂ) r, u x • a x ∂(muPi β (Fin d)) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : a x = 0 := by
      by_contra hne
      exact hx (hsupp hne)
    rw [this, smul_zero]
  rw [h1]
  refine norm_setIntegral_le_of_norm_le_const (isCompact_closedBall _ _).measure_lt_top ?_
  intro x _
  rw [norm_smul, hu, one_mul]
  exact hS x
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
