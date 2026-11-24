-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_H_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:10.510462+00:00
-- url     : https://prove2.me/submissions/88b7bfab-987e-450c-b328-fbe64ec5672e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_hasFDerivAt_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_dg_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_B_eq

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
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hdg0 : ∀ k, dg 0 k = 0)
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0)
    (hgrad : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) (x : Fin d → ℂ) :
    ‖x‖ ≤ Λ * ‖H *ᵥ x‖ := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have hline : HasDerivAt (fun ε : ℝ => ε • x) x 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const x
  have hcl : ContinuousAt (fun ε : ℝ => ε • x) 0 := hline.continuousAt
  have hf : HasDerivAt (fun ε : ℝ => dg (ε • x)) (H *ᵥ x) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have h2 : HasFDerivAt (fun y => fderiv ℂ g y (Pi.single i 1))
        (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp (fderiv ℂ (fderiv ℂ g) 0)).restrictScalars ℝ)
        ((0:ℝ) • x) := by
      rw [zero_smul]; exact (F_hasFDerivAt_apply hr hg _).restrictScalars ℝ
    have h3 := h2.comp_hasDerivAt (0:ℝ) hline
    have hval : (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp
        (fderiv ℂ (fderiv ℂ g) 0)).restrictScalars ℝ) x = (H *ᵥ x) i := by
      show fderiv ℂ (fderiv ℂ g) 0 x (Pi.single i 1) = _
      rw [F_B_eq hr hg hdg hH]
      simp [dotProduct, Pi.single_apply]
    rw [hval] at h3
    refine h3.congr_of_eventuallyEq ?_
    have : ∀ᶠ ε in 𝓝 (0:ℝ), ε • x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) :=
      hcl.eventually_mem (by rw [zero_smul]; exact Metric.isOpen_ball.mem_nhds h0)
    filter_upwards [this] with ε hε
    exact (F_dg_eq hg hdg hε i).symm
  have ht := hf.tendsto_slope_zero_right
  have hd0 : dg ((0:ℝ) • x) = 0 := by rw [zero_smul]; funext k; exact hdg0 k
  have ht2 : Tendsto (fun ε : ℝ => Λ * ‖ε⁻¹ • (dg ((0 + ε) • x) - dg ((0:ℝ) • x))‖) (𝓝[>] 0)
      (𝓝 (Λ * ‖H *ᵥ x‖)) := (ht.norm).const_mul Λ
  refine ge_of_tendsto ht2 ?_
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε • x ∈ Metric.closedBall (0 : Fin d → ℂ) r :=
    (hcl.eventually_mem (by rw [zero_smul]; exact Metric.closedBall_mem_nhds _ hr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0:ℝ) < ε := hpos
  have h1 := hgrad _ hε
  rw [hd0, sub_zero, zero_add, norm_smul, norm_inv, Real.norm_of_nonneg hpos'.le]
  rw [norm_smul, Real.norm_of_nonneg hpos'.le] at h1
  calc ‖x‖ = ε⁻¹ * (ε * ‖x‖) := by field_simp
    _ ≤ ε⁻¹ * (Λ * ‖dg (ε • x)‖) := by gcongr
    _ = Λ * (ε⁻¹ * ‖dg (ε • x)‖) := by ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
