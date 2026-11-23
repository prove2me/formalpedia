-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:00.97934+00:00
-- url     : https://prove2.me/submissions/01bb1cf0-db7e-45f8-be8b-b3d088c0be29

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_bilC_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_dirv_false
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_dirv_true

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
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hH : ∀ i j, ‖H i j‖ ≤ Γ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hlow : ∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) (x : Fin d → ℂ) :
    ∃ l : Fin d × Bool, ‖c‖ / (4 * Λ) * ‖x‖ ≤ |fderiv ℝ (D_phi d c H) x (dirv l)| := by
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  by_contra hcon
  push Not at hcon
  have hx0 : 0 < ‖x‖ := by
    have := hcon (⟨0, hd⟩, false)
    have h2 := (abs_nonneg _).trans_lt this
    by_contra h3
    have h4 : ‖x‖ = 0 := le_antisymm (not_lt.1 h3) (norm_nonneg x)
    rw [h4, mul_zero] at h2
    exact lt_irrefl _ h2
  have hk : ∀ k, ‖(H *ᵥ x) k‖ ≤ ‖x‖ / (2 * Λ) := by
    intro k
    have h1 := hcon (k, false)
    have h2 := hcon (k, true)
    rw [D_phi_fderiv d c H hs Γ hΓ hH] at h1 h2
    simp only [D_bilC_apply, D_dirv_false, D_dirv_true] at h1 h2
    have h3 : (c * (Complex.I * (H *ᵥ x) k)).re = - (c * (H *ᵥ x) k).im := by
      have : c * (Complex.I * (H *ᵥ x) k) = Complex.I * (c * (H *ᵥ x) k) := by ring
      rw [this, Complex.I_mul_re]
    rw [h3, abs_neg] at h2
    have h4 : ‖c * (H *ᵥ x) k‖ ≤ |(c * (H *ᵥ x) k).re| + |(c * (H *ᵥ x) k).im| := Complex.norm_le_abs_re_add_abs_im _
    rw [norm_mul] at h4
    have h5 : ‖c‖ * ‖(H *ᵥ x) k‖ ≤ ‖c‖ * (‖x‖ / (2 * Λ)) := by
      have : ‖c‖ * (‖x‖ / (2 * Λ)) = ‖c‖ / (4 * Λ) * ‖x‖ + ‖c‖ / (4 * Λ) * ‖x‖ := by field_simp; ring
      rw [this]
      linarith
    exact le_of_mul_le_mul_left h5 hc0
  have h6 : ‖H *ᵥ x‖ ≤ ‖x‖ / (2 * Λ) := (pi_norm_le_iff_of_nonneg (by positivity)).2 hk
  have h7 := hlow x
  have h8 : Λ * ‖H *ᵥ x‖ ≤ ‖x‖ / 2 := by
    calc Λ * ‖H *ᵥ x‖ ≤ Λ * (‖x‖ / (2 * Λ)) := by gcongr
      _ = ‖x‖ / 2 := by field_simp
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
