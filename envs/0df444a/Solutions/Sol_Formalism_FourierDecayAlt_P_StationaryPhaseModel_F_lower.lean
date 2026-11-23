-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:16.394529+00:00
-- url     : https://prove2.me/submissions/5f108b31-c79a-4769-a5fc-d684851fce3b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_dg_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_mem_ball
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_fderiv

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
theorem _root_.solution (hd : 0 < d) (hr : 0 < r) (hΛ : 0 < Λ) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hgrad : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) {c : ℂ} (hc : c ≠ 0)
    {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    ∃ l : Fin d × Bool, ‖c‖ / (2 * Λ) * ‖x‖ ≤ |fderiv ℝ (F_phi d r c g) x (dirv l)| := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hx1 := F_mem_ball hr hx
  have hx2 : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.ball_subset_ball (by linarith) hx1
  by_cases hx0 : ‖x‖ = 0
  · exact ⟨(⟨0, hd⟩, false), by rw [hx0, mul_zero]; exact abs_nonneg _⟩
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
  by_contra hcon
  push Not at hcon
  have hk : ∀ k, ‖dg x k‖ < ‖x‖ / Λ := by
    intro k
    have h1 := hcon (k, false)
    have h2 := hcon (k, true)
    rw [F_phi_fderiv hr hg c hx1] at h1 h2
    have e1 : fderiv ℂ g x (dirv (k, false)) = dg x k := by
      simp only [dirv]; exact F_dg_eq hg hdg hx2 k
    have e2 : fderiv ℂ g x (dirv (k, true)) = Complex.I * dg x k := by
      have : (dirv (k, true) : Fin d → ℂ) = Complex.I • Pi.single k 1 := by
        simp only [dirv]
        rw [← Pi.single_smul]; simp
      rw [this, map_smul, F_dg_eq hg hdg hx2 k, smul_eq_mul]
    rw [e1] at h1
    rw [e2] at h2
    have e3 : (c * (Complex.I * dg x k)).re = -(c * dg x k).im := by
      have : c * (Complex.I * dg x k) = Complex.I * (c * dg x k) := by ring
      rw [this, Complex.I_mul_re]
    rw [e3, abs_neg] at h2
    have h3 : ‖c * dg x k‖ ≤ |(c * dg x k).re| + |(c * dg x k).im| := Complex.norm_le_abs_re_add_abs_im _
    rw [norm_mul] at h3
    have h4 : ‖c‖ * ‖dg x k‖ < ‖c‖ * (‖x‖ / Λ) := by
      calc ‖c‖ * ‖dg x k‖ ≤ _ := h3
        _ < ‖c‖ / (2 * Λ) * ‖x‖ + ‖c‖ / (2 * Λ) * ‖x‖ := add_lt_add h1 h2
        _ = ‖c‖ * (‖x‖ / Λ) := by field_simp; ring
    exact lt_of_mul_lt_mul_left h4 hcpos.le
  have h5 : ‖dg x‖ < ‖x‖ / Λ := (pi_norm_lt_iff (by positivity)).2 hk
  have h6 := hgrad x hx
  have h7 : Λ * ‖dg x‖ < ‖x‖ := by
    calc Λ * ‖dg x‖ < Λ * (‖x‖ / Λ) := by gcongr
      _ = ‖x‖ := by field_simp
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
