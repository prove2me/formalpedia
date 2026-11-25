-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_bounded_of_fourier_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:36.298831+00:00
-- url     : https://prove2.me/submissions/f2deb5eb-14aa-407e-95dd-e84335de5161

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MomentIntegrable
import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothBoundedOfFourierDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_integral_fsv_eq_fourier
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_fourier_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex
open scoped FourierTransform ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by
  refine fourier_smooth D m C hD fun w => ?_
  rw [Complex.finrank_real_complex]
  set s : ℂ := -(I * π * conj w) with hs
  have hw : w = -(I * conj s) / (π : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hs]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hns : ‖s‖ = π * ‖w‖ := by
    rw [hs, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have h := hdec s
  rw [integral_fsv_eq_fourier, ← hw] at h
  refine h.trans ?_
  have hC : 0 ≤ C := by
    have h0 := (norm_nonneg _).trans (hdec 0)
    exact nonneg_of_mul_nonneg_left h0 (by positivity)
  have e : (-((m : ℝ) + ((2 : ℕ) : ℝ) + 1)) = -((m : ℝ) + 3) := by push_cast; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  rw [hns]
  nlinarith [Real.pi_gt_three, norm_nonneg w]
end Formalism.FourierDecayAlt.P5.HerC.Fou
