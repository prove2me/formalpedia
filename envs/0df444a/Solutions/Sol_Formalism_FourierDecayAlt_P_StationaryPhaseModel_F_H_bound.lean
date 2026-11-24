-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_H_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:33.124372+00:00
-- url     : https://prove2.me/submissions/c30876bc-bfea-4d2d-9773-e989a15d7eff

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_norm_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_diff_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_hasFDerivAt_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_H_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_norm_fderiv_le

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
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hb : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ)
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) (i j : Fin d) :
    ‖H i j‖ ≤ Λ / (r / 2) / (r / 2) := by
  have hsub : Metric.ball (0 : Fin d → ℂ) (2 * (r / 2)) ⊆ Metric.ball (0 : Fin d → ℂ) (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hp : DifferentiableOn ℂ (fun y => fderiv ℂ g y (Pi.single i 1)) (Metric.ball 0 (2 * (r / 2))) := by
    intro y hy
    exact (((F_diff_fderiv hg) y (hsub hy)).clm_apply (differentiableWithinAt_const _)).mono hsub
  have hpb : ∀ y ∈ Metric.ball (0 : Fin d → ℂ) (2 * (r / 2)), ‖fderiv ℂ g y (Pi.single i 1)‖ ≤ Λ / (r / 2) := by
    intro y hy
    have hs : Metric.ball y (2 * (r / 2)) ⊆ Metric.ball (0 : Fin d → ℂ) (2 * r) := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hy ⊢
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by simpa using norm_add_le (z - y) y
      linarith
    have := F_norm_fderiv_le (half_pos hr) (hg.mono hs) (fun z hz => hb z (hs hz)) (Pi.single i 1)
    simpa [F_norm_single] using this
  have h1 := F_norm_fderiv_le (half_pos hr) hp hpb (Pi.single j 1)
  have h2 : fderiv ℂ (fun y => fderiv ℂ g y (Pi.single i 1)) 0 (Pi.single j 1) = H i j := by
    rw [(F_hasFDerivAt_apply hr hg (Pi.single i 1)).fderiv]
    exact F_H_eq hr hg hdg hH i j
  rw [h2] at h1
  simpa [F_norm_single] using h1
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
