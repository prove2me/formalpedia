-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.model
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:18.598399+00:00
-- url     : https://prove2.me/submissions/a968d973-a723-44de-87ec-061995890625

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_compare
import Theorems.Thm_Formalism_FourierDecayAlt_P_gaussian_multi_integral


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
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (ρ Γ Λ : ℝ) (hρ : 0 < ρ) (hΓ : 0 < Γ) (hΛ : 0 < Λ) : ∃ C : ℝ,
    ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsSymm → (∀ i j, ‖H i j‖ ≤ Γ) → (∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) →
      ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 →
        ‖∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) -
            ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)‖ ≤ C * ‖t‖ ^ (d + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, ?_⟩
    intro H _ _ _ t _ _
    have h1 : muPi β (Fin 0) = Measure.dirac (0 : Fin 0 → ℂ) := by
      unfold muPi
      exact Measure.pi_of_empty _ _
    rw [h1, integral_dirac, D_cut_one 0 hρ (by simp; positivity), Matrix.det_isEmpty]
    simp [psi]
  · obtain ⟨C, hC⟩ := D_compare d hd β hβ ρ Γ Λ hρ hΓ hΛ
    refine ⟨C, ?_⟩
    intro H hs hH hlow t ht ht1
    have hdet : H.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      have := hlow v
      rw [hHv, norm_zero, mul_zero] at this
      exact hv (norm_le_zero_iff.1 this)
    have hG := gaussian_multi_integral d β t H hβ ht hs hdet
    have hlim := (tendsto_const_nhds (x := ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) *
      ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))).sub hG).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with δ hδ
    exact hC H hs hH hlow t ht ht1 δ hδ.1 hδ.2
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
