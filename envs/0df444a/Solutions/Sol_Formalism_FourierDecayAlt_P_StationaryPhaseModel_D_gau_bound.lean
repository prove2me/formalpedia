-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:56.354868+00:00
-- url     : https://prove2.me/submissions/eb246826-0764-4a66-a328-59d832c4d127

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_one_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_scale

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
theorem _root_.solution (d N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    (∀ x : Fin d → ℂ, ∀ i ≤ N, ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ ≤ M) ∧
    Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N M (D_gau d δ) := by
  choose c hc0 hc using D_gau_one_bound d
  refine ⟨∑ i ∈ Finset.range (N + 1), c i, Finset.sum_nonneg fun i _ => hc0 i, ?_⟩
  intro δ hδ hδ1 σ hσ hσ1
  have hci : ∀ i ≤ N, c i ≤ ∑ i ∈ Finset.range (N + 1), c i := fun i hi =>
    Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_range.2 (by omega))
  set a := Real.sqrt δ with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 hδ
  have ha1 : a ≤ 1 := Real.sqrt_le_one.2 hδ1
  have hder : ∀ (i : ℕ) (x : Fin d → ℂ), ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ =
      a ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
    intro i x
    rw [D_gau_scale d δ hδ.le, iteratedFDeriv_comp_const_smul a (D_gau_contDiff d 1 i), norm_smul, norm_pow,
      Real.norm_of_nonneg ha0.le]
  have hkey : ∀ (i : ℕ) (x : Fin d → ℂ), (‖x‖ + σ) ^ i * ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ ≤ c i := by
    intro i x
    rw [hder]
    calc (‖x‖ + σ) ^ i * (a ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖)
        = (a * ‖x‖ + a * σ) ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
          rw [← mul_assoc, ← mul_pow]; congr 2; ring
      _ ≤ (1 + ‖a • x‖) ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
          have h5 : a * ‖x‖ + a * σ ≤ 1 + ‖a • x‖ := by
            rw [norm_smul, Real.norm_of_nonneg ha0.le]
            have : a * σ ≤ 1 := by nlinarith
            linarith
          have h6 : 0 ≤ a * ‖x‖ + a * σ := by positivity
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h6 h5 i) (norm_nonneg _)
      _ ≤ c i := hc i _
  refine ⟨fun x i hi => ?_, D_gau_contDiff d δ N, fun x _ i hi => ?_⟩
  · rw [hder]
    have h1 := hc i (a • x)
    have h2 : (1 : ℝ) ≤ (1 + ‖a • x‖) ^ i := one_le_pow₀ (by linarith [norm_nonneg (a • x)])
    have h3 : a ^ i ≤ 1 := pow_le_one₀ ha0.le ha1
    calc a ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖
        ≤ (1 + ‖a • x‖) ^ i * ‖iteratedFDeriv ℝ i (D_gau d 1) (a • x)‖ := by
          exact mul_le_mul_of_nonneg_right (h3.trans h2) (norm_nonneg _)
      _ ≤ _ := h1.trans (hci i hi)
  · have hw : 0 < wt σ x := D_wt_pos hσ x
    rw [zero_sub, _root_.zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact (hkey i x).trans (hci i hi)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
