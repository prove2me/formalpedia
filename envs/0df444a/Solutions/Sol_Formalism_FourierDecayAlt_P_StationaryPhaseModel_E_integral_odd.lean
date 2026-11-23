-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_integral_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:40.936949+00:00
-- url     : https://prove2.me/submissions/4204bdc0-5cb8-4b8a-94da-716c7e1d4ef8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_integral_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hβ : β ≠ 0) (f : (Fin d → ℂ) → V) (hf : ∀ x, f (-x) = - f x) :
    ∫ x, f x ∂(muPi β (Fin d)) = 0 := by
  have h := E_integral_neg hβ f
  simp_rw [hf] at h
  rw [integral_neg] at h
  have h2 : (2 : ℝ) • ∫ x, f x ∂(muPi β (Fin d)) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    simp
  exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
