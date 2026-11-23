-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_dil_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:41.506392+00:00
-- url     : https://prove2.me/submissions/71278cae-7212-4c51-aa76-598e79c5c6f7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_wt_pos

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {N : ℕ} {h : E → F} {ρ₀ M : ℝ} (hh : ContDiff ℝ N h)
    (hs : tsupport h ⊆ Metric.closedBall 0 ρ₀) (hρ₀ : 0 ≤ ρ₀) (hM : ∀ x, ∀ i ≤ N, ‖iteratedFDeriv ℝ i h x‖ ≤ M)
    {R σ : ℝ} (hR : 1 ≤ R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Sym Set.univ (wt σ) 0 N (M * (ρ₀ + 1) ^ N) (fun x => h (R⁻¹ • x)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0 (Nat.zero_le _))
  have hR0 : 0 < R := by linarith
  refine ⟨hh.comp (contDiff_const_smul _), fun x _ i hi => ?_⟩
  have hw : 0 < wt σ x := D_wt_pos hσ x
  rw [iteratedFDeriv_comp_const_smul R⁻¹ (hh.of_le (by exact_mod_cast hi)), norm_smul, norm_pow,
    Real.norm_of_nonneg (inv_pos.2 hR0).le]
  by_cases hx : R⁻¹ • x ∈ tsupport h
  · have h1 : ‖R⁻¹ • x‖ ≤ ρ₀ := by simpa using hs hx
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hR0).le, inv_mul_le_iff₀ hR0] at h1
    have h2 : wt σ x ≤ (ρ₀ + 1) * R := by unfold wt; nlinarith
    have h3 : R⁻¹ * wt σ x ≤ ρ₀ + 1 := by rw [inv_mul_le_iff₀ hR0]; linarith
    have h4 : (R⁻¹ * wt σ x) ^ i ≤ (ρ₀ + 1) ^ N :=
      (pow_le_pow_left₀ (by positivity) h3 i).trans (pow_le_pow_right₀ (by linarith) hi)
    rw [zero_sub, _root_.zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc R⁻¹ ^ i * ‖iteratedFDeriv ℝ i h (R⁻¹ • x)‖ * wt σ x ^ i
        = ‖iteratedFDeriv ℝ i h (R⁻¹ • x)‖ * (R⁻¹ * wt σ x) ^ i := by rw [mul_pow]; ring
      _ ≤ M * (ρ₀ + 1) ^ N := mul_le_mul (hM _ i hi) h4 (by positivity) hM0
  · have h1 : R⁻¹ • x ∉ tsupport (iteratedFDeriv ℝ i h) := fun h => hx (tsupport_iteratedFDeriv_subset i h)
    rw [image_eq_zero_of_notMem_tsupport h1, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (zpow_nonneg hw.le _)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
