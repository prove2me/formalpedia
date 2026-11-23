-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.bump_cutoff_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:42.930626+00:00
-- url     : https://prove2.me/submissions/19f6aeb1-d6c5-4980-8801-455706462bd5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_cutoff_eq_contDiffBump

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
theorem _root_.solution (d : ℕ) (ρ : ℝ) (h : 0 < ρ) (n : ℕ) :
    ContDiff ℝ n (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ∧
    HasCompactSupport (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ∧
    Function.support (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ⊆ Metric.closedBall 0 ρ ∧
    ((cutB d ρ (0 : Fin d → ℂ) : ℝ) : ℂ) = 1 := by
  rw [cutoff_eq_contDiffBump d ρ h]
  set f : ContDiffBump (0 : Fin d → ℂ) := ⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ with hf
  have hc : ContDiff ℝ n (fun x : Fin d → ℂ => ((f x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (f.contDiff (n := (n : ℕ∞)))
  have hsupp : Function.support (fun x : Fin d → ℂ => ((f x : ℝ) : ℂ)) = Metric.ball 0 ρ := by
    rw [← f.support_eq]
    ext x
    simp [Function.mem_support]
  refine ⟨hc, ?_, ?_, ?_⟩
  · have : HasCompactSupport (fun x : Fin d → ℂ => f x) := f.hasCompactSupport
    exact this.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)
  · rw [hsupp]; exact Metric.ball_subset_closedBall
  · have : f 0 = 1 := f.one_of_mem_closedBall (by simpa [hf] using (half_pos h).le)
    simp [this]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
