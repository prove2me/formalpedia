-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.J_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:53.602457+00:00
-- url     : https://prove2.me/submissions/6b02d6d9-91c5-48cd-bf6c-8c0a073a5a46

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_ee_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_ee_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_ibp2
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_hasDerivAt_g0
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_hasDerivAt_g1
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_continuousOn_g2_symmetric_interval

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
theorem _root_.solution {u : ℝ} (hu : 1 ≤ u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by
  have hu0 : 0 < u := by linarith
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hsu2 : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  set a : ℝ := 1 - 1 / u with ha
  have hia : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
  have hia0 : 0 < 1 / u := by positivity
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  have hcont : Continuous fun t => (g0 t : ℂ) * ee u t := by
    unfold g0; exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2)))).mul (ee_cont u)
  have hii : ∀ x y : ℝ, IntervalIntegrable (fun t => (g0 t : ℂ) * ee u t) volume x y :=
    fun x y => hcont.intervalIntegrable x y
  rw [← integral_add_adjacent_intervals (hii (-1) (-a)) (hii (-a) 1),
    ← integral_add_adjacent_intervals (hii (-a) a) (hii a 1)]

  have hsq2 : Real.sqrt (2 / u) = Real.sqrt 2 / Real.sqrt u := Real.sqrt_div' 2 hu0.le
  have hend : ∀ t : ℝ, 1 - t ^ 2 ≤ 2 / u → ‖(g0 t : ℂ) * ee u t‖ ≤ Real.sqrt 2 / Real.sqrt u := by
    intro t ht
    unfold g0
    rw [norm_mul, ee_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← hsq2]
    exact Real.sqrt_le_sqrt ht
  have b1 : ‖∫ t in (-1 : ℝ)..(-a), (g0 t : ℂ) * ee u t‖ ≤ Real.sqrt 2 / Real.sqrt u * (1 / u) := by
    refine (norm_integral_le_of_norm_le_const fun t ht => hend t ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le (by linarith)] at ht
      have h1 : 0 ≤ 1 + t := by linarith [ht.1]
      have h2 : 1 + t ≤ 1 / u := by linarith [ht.2]
      have h3 : 1 - t ≤ 2 := by linarith [ht.1]
      have : 1 - t ^ 2 = (1 + t) * (1 - t) := by ring
      rw [this, div_eq_mul_one_div 2 u]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]; ring
  have b3 : ‖∫ t in a..1, (g0 t : ℂ) * ee u t‖ ≤ Real.sqrt 2 / Real.sqrt u * (1 / u) := by
    refine (norm_integral_le_of_norm_le_const fun t ht => hend t ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le (by linarith)] at ht
      have h1 : 0 ≤ 1 - t := by linarith [ht.2]
      have h2 : 1 - t ≤ 1 / u := by linarith [ht.1]
      have h3 : 1 + t ≤ 2 := by linarith [ht.2]
      have : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
      rw [this, div_eq_mul_one_div 2 u]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]; ring

  have hin : ∀ x ∈ uIcc (-a) a, x ^ 2 < 1 := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    nlinarith [hx.1, hx.2]
  have b2 := ibp2 (φ := g0) (φ' := g1) (φ'' := g2) (α := -a) (β := a) (by linarith) hu0
    (fun x hx => hasDerivAt_g0 (hin x hx)) (fun x hx => hasDerivAt_g1 (hin x hx)) (continuousOn_g2_symmetric_interval ha1 ha0)

  have hpa : 0 < 1 - a ^ 2 := by nlinarith
  set s := Real.sqrt (1 - a ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpa
  have hslo : 1 / Real.sqrt u ≤ s := by
    have e1 : 1 / Real.sqrt u = Real.sqrt (1 / u) := by rw [Real.sqrt_div' 1 hu0.le, Real.sqrt_one]
    rw [hs, e1]
    apply Real.sqrt_le_sqrt
    rw [ha]
    have : 1 - (1 - 1 / u) ^ 2 = 1 / u * (2 - 1 / u) := by ring
    rw [this]
    nlinarith
  have hshi : s ≤ Real.sqrt 2 / Real.sqrt u := by
    rw [hs, ← hsq2]
    apply Real.sqrt_le_sqrt
    rw [ha]
    have : 1 - (1 - 1 / u) ^ 2 = 1 / u * (2 - 1 / u) := by ring
    rw [this, div_eq_mul_one_div 2 u]
    nlinarith
  have hg0a : |g0 (-a)| + |g0 a| ≤ 2 * (Real.sqrt 2 / Real.sqrt u) := by
    simp only [g0, neg_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← hs]; linarith
  have hinv : 1 / s ≤ Real.sqrt u := by
    rw [div_le_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left hslo hsu.le
    rw [mul_one_div_cancel hsu.ne'] at this
    linarith
  have hg1a : |g1 (-a)| + |g1 a| ≤ 2 * Real.sqrt u := by
    simp only [g1, neg_sq, neg_neg, abs_div, abs_neg, abs_of_nonneg ha0, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← hs]
    have : a / s ≤ 1 / s := div_le_div_of_nonneg_right (by linarith) hs0.le
    linarith

  have hint : ∫ t in (-a)..a, |g2 t| = 2 * (a / s) := by
    have e : ∫ t in (-a)..a, |g2 t| = ∫ t in (-a)..a, -g2 t := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx2 := hin x hx
      have hp : 0 < 1 - x ^ 2 := by linarith
      have : g2 x ≤ 0 := by
        simp only [g2]
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg hp.le (Real.sqrt_nonneg _))
      simp only
      rw [abs_of_nonpos this]
    rw [e, intervalIntegral.integral_neg, integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_g1 (hin x hx))
      ((continuousOn_g2_symmetric_interval ha1 ha0).intervalIntegrable)]
    simp only [g1, neg_sq, neg_neg]
    rw [← hs]; ring
  have hint' : ∫ t in (-a)..a, |g2 t| ≤ 2 * Real.sqrt u := by
    rw [hint]
    have : a / s ≤ 1 / s := div_le_div_of_nonneg_right (by linarith) hs0.le
    linarith

  have hm : ‖∫ t in (-a)..a, (g0 t : ℂ) * ee u t‖ ≤ (2 * Real.sqrt 2 + 4) / (u * Real.sqrt u) := by
    refine b2.trans ?_
    have k1 : (|g0 (-a)| + |g0 a|) / u ≤ 2 * Real.sqrt 2 / (u * Real.sqrt u) := by
      rw [div_le_div_iff₀ hu0 (by positivity)]
      have := mul_le_mul_of_nonneg_right hg0a (by positivity : 0 ≤ u * Real.sqrt u)
      calc (|g0 (-a)| + |g0 a|) * (u * Real.sqrt u) ≤ 2 * (Real.sqrt 2 / Real.sqrt u) * (u * Real.sqrt u) := this
        _ = 2 * Real.sqrt 2 * u := by field_simp
    have k2 : ((|g1 (-a)| + |g1 a|) + ∫ t in (-a)..a, |g2 t|) / u ^ 2 ≤ 4 / (u * Real.sqrt u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := add_le_add hg1a hint'
      have h4 := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ u * Real.sqrt u)
      calc ((|g1 (-a)| + |g1 a|) + ∫ t in (-a)..a, |g2 t|) * (u * Real.sqrt u)
          ≤ (2 * Real.sqrt u + 2 * Real.sqrt u) * (u * Real.sqrt u) := h4
        _ = 4 * u ^ 2 := by rw [show (2 * Real.sqrt u + 2 * Real.sqrt u) * (u * Real.sqrt u) =
              4 * u * (Real.sqrt u * Real.sqrt u) by ring, hsu2]; ring
    have : 2 * Real.sqrt 2 / (u * Real.sqrt u) + 4 / (u * Real.sqrt u) = (2 * Real.sqrt 2 + 4) / (u * Real.sqrt u) := by
      ring
    linarith
  have hends : Real.sqrt 2 / Real.sqrt u * (1 / u) = Real.sqrt 2 / (u * Real.sqrt u) := by field_simp
  have h22 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc ‖(∫ t in (-1 : ℝ)..(-a), (g0 t : ℂ) * ee u t) + ((∫ t in (-a)..a, (g0 t : ℂ) * ee u t) +
        ∫ t in a..1, (g0 t : ℂ) * ee u t)‖
      ≤ ‖∫ t in (-1 : ℝ)..(-a), (g0 t : ℂ) * ee u t‖ + (‖∫ t in (-a)..a, (g0 t : ℂ) * ee u t‖ +
        ‖∫ t in a..1, (g0 t : ℂ) * ee u t‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ Real.sqrt 2 / (u * Real.sqrt u) + ((2 * Real.sqrt 2 + 4) / (u * Real.sqrt u) +
        Real.sqrt 2 / (u * Real.sqrt u)) := by rw [← hends]; gcongr
    _ = (4 * Real.sqrt 2 + 4) / (u * Real.sqrt u) := by ring
    _ ≤ 10 / (u * Real.sqrt u) := by
        apply div_le_div_of_nonneg_right _ (by positivity); linarith
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
