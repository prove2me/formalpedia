-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.ibp2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:23.747408+00:00
-- url     : https://prove2.me/submissions/c54b0669-4aca-405f-83af-2baf03b558f3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_ee_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_hasDerivAt_V
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_norm_V

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {φ φ' φ'' : ℝ → ℝ} {α β u : ℝ} (hαβ : α ≤ β) (hu : 0 < u)
    (h1 : ∀ x ∈ uIcc α β, HasDerivAt φ (φ' x) x) (h2 : ∀ x ∈ uIcc α β, HasDerivAt φ' (φ'' x) x)
    (h3 : ContinuousOn φ'' (uIcc α β)) :
    ‖∫ t in α..β, (φ t : ℂ) * ee u t‖ ≤
      (|φ α| + |φ β|) / u + ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 := by
  set V : ℝ → ℂ := fun t => ee u t / (Complex.I * u) with hV
  have hVd : ∀ x ∈ uIcc α β, HasDerivAt V (ee u x) x := fun x _ => hasDerivAt_V hu.ne' x
  have hφ'c : ContinuousOn φ' (uIcc α β) := fun x hx => (h2 x hx).continuousAt.continuousWithinAt
  have hi1 : IntervalIntegrable (fun t => (φ' t : ℂ)) volume α β :=
    (Complex.continuous_ofReal.comp_continuousOn hφ'c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => (φ'' t : ℂ)) volume α β :=
    (Complex.continuous_ofReal.comp_continuousOn h3).intervalIntegrable
  have hie : IntervalIntegrable (ee u) volume α β := (ee_cont u).intervalIntegrable _ _
  have e1 := integral_mul_deriv_eq_deriv_mul (u := fun t => (φ t : ℂ)) (v := V) (u' := fun t => (φ' t : ℂ))
    (v' := ee u) (fun x hx => (h1 x hx).ofReal_comp) hVd hi1 hie
  have e2 := integral_mul_deriv_eq_deriv_mul (u := fun t => (φ' t : ℂ)) (v := V) (u' := fun t => (φ'' t : ℂ))
    (v' := ee u) (fun x hx => (h2 x hx).ofReal_comp) hVd hi2 hie
  have e3 : ∫ t in α..β, (φ' t : ℂ) * V t = (∫ t in α..β, (φ' t : ℂ) * ee u t) / (Complex.I * u) := by
    rw [← intervalIntegral.integral_div]; congr 1; funext t; simp only [hV]; ring
  have hVn := norm_V hu
  have hu2 : 0 < u ^ 2 := by positivity

  have b3 : ‖∫ t in α..β, (φ'' t : ℂ) * V t‖ ≤ (∫ t in α..β, |φ'' t|) / u := by
    refine (intervalIntegral.norm_integral_le_integral_norm hαβ).trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_div]
    congr 1; funext t
    rw [norm_mul, hVn, Complex.norm_real, Real.norm_eq_abs]; ring
  have b2 : ‖∫ t in α..β, (φ' t : ℂ) * ee u t‖ ≤ (|φ' α| + |φ' β|) / u + (∫ t in α..β, |φ'' t|) / u := by
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
    rw [norm_mul, norm_mul, hVn, hVn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have := b3
    have e : |φ' β| * (1 / u) + |φ' α| * (1 / u) = (|φ' α| + |φ' β|) / u := by ring
    linarith
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  rw [norm_mul, norm_mul, hVn, hVn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, e3,
    norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have b2' : ‖∫ t in α..β, (φ' t : ℂ) * ee u t‖ / u ≤ ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 := by
    rw [div_le_iff₀ hu]
    calc ‖∫ t in α..β, (φ' t : ℂ) * ee u t‖ ≤ (|φ' α| + |φ' β|) / u + (∫ t in α..β, |φ'' t|) / u := b2
      _ = ((|φ' α| + |φ' β|) + ∫ t in α..β, |φ'' t|) / u ^ 2 * u := by field_simp
  have e : |φ β| * (1 / u) + |φ α| * (1 / u) = (|φ α| + |φ β|) / u := by ring
  linarith
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
