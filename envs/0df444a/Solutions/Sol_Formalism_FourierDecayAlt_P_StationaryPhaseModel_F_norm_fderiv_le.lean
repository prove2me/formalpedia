-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_norm_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:38.778441+00:00
-- url     : https://prove2.me/submissions/886bee9a-69ce-4f48-bf01-22009cde30ad

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_holo_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {f : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.ball x (2 * δ))) (hM : ∀ y ∈ Metric.ball x (2 * δ), ‖f y‖ ≤ M)
    (v : Fin d → ℂ) : ‖fderiv ℂ f x v‖ ≤ M / δ * ‖v‖ := by
  have h1 := holo_bound 1 (f := f) (x := x) (δ := δ) (M := M) hδ (by simpa [one_add_one_eq_two] using hf)
    (by simpa [one_add_one_eq_two] using hM)
  rw [norm_iteratedFDeriv_one, pow_one] at h1
  have hx : x ∈ Metric.ball x (2 * δ) := Metric.mem_ball_self (by positivity)
  have h2 : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ :=
    (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hx)).fderiv_restrictScalars ℝ
  have h3 : fderiv ℂ f x v = fderiv ℝ f x v := by rw [h2]; rfl
  rw [h3]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
