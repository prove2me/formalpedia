-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.disc_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:43:37.082855+00:00
-- url     : https://prove2.me/submissions/64ab951d-49a5-40dd-8543-9d93dee5bc8c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_J_all
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_disc_fubini
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_disc_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.DiscMean := by
  intro β hβ
  refine ⟨20 / Real.pi * ‖β‖ ^ (-(3 / 2 : ℝ)), fun ξ x₀ R hξ hR => ?_⟩
  classical
  set γ := β * ξ with hγ
  have hγ0 : γ ≠ 0 := mul_ne_zero hβ hξ
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
  set c : ℝ := ‖γ‖ with hc
  have hpsi : ∀ x : ℂ, G.psi β (ξ * x) = Complex.exp (Complex.I * ((γ * x).re : ℂ)) := by
    intro x
    simp only [G.psi, hγ, mul_assoc]
  have htr : ∫ x in ball x₀ R, G.psi β (ξ * x) =
      Complex.exp (Complex.I * ((γ * x₀).re : ℂ)) *
        ∫ w in ball (0 : ℂ) R, Complex.exp (Complex.I * ((γ * w).re : ℂ)) := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← integral_const_mul, ← integral_add_left_eq_self _ x₀]
    congr 1
    funext w
    by_cases hw : w ∈ ball (0 : ℂ) R
    · have hw' : x₀ + w ∈ ball x₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hw
      rw [Set.indicator_of_mem hw', Set.indicator_of_mem hw, hpsi, mul_add, Complex.add_re,
        Complex.ofReal_add, mul_add, Complex.exp_add]
    · have hw' : x₀ + w ∉ ball x₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hw
      rw [Set.indicator_of_notMem hw', Set.indicator_of_notMem hw, mul_zero]
  set u : Circle := Circle.exp (-Complex.arg γ) with hu
  have hrot : ∀ v : ℂ, γ * (rotation u v) = (c : ℂ) * v := by
    intro v
    rw [rotation_apply, hu, Circle.coe_exp]
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I γ]
    calc (↑‖γ‖ * Complex.exp (↑γ.arg * Complex.I)) * (Complex.exp (↑(-γ.arg) * Complex.I) * v)
        = ↑‖γ‖ * (Complex.exp (↑γ.arg * Complex.I) * Complex.exp (↑(-γ.arg) * Complex.I)) * v := by
          ring
      _ = ↑‖γ‖ * v := by
          rw [← Complex.exp_add, Complex.ofReal_neg, neg_mul, add_neg_cancel, Complex.exp_zero,
            mul_one]
  have hrotI : ∫ w in ball (0 : ℂ) R, Complex.exp (Complex.I * ((γ * w).re : ℂ)) =
      ∫ v in ball (0 : ℂ) R, ee c v.re := by
    have hL := LinearIsometryEquiv.measurePreserving (rotation u)
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← hL.integral_comp (rotation u).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    have hn : rotation u v ∈ ball (0 : ℂ) R ↔ v ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
    by_cases hv : v ∈ ball (0 : ℂ) R
    · rw [Set.indicator_of_mem (hn.mpr hv), Set.indicator_of_mem hv, hrot, Complex.re_ofReal_mul]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hv (hn.mp h)), Set.indicator_of_notMem hv]
  have hvol : (volume (ball x₀ R)).toReal = R ^ 2 * Real.pi := by
    rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
    simp
  have hJ := J_all (u := c * R) (by positivity)
  have hx : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hy : 0 < R * ‖ξ‖ := mul_pos hR (norm_pos_iff.mpr hξ)
  have hcR : c * R = ‖β‖ * (R * ‖ξ‖) := by
    rw [hc, hγ, norm_mul]
    ring
  have hpow : c * R * Real.sqrt (c * R) = (‖β‖ * (R * ‖ξ‖)) ^ (3 / 2 : ℝ) := by
    rw [hcR, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one]
  have hkey : 10 / (c * R * Real.sqrt (c * R)) =
      10 * (‖β‖ ^ (-(3 / 2 : ℝ)) * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ))) := by
    rw [hpow, ← Real.mul_rpow hx.le hy.le, Real.rpow_neg (by positivity), div_eq_mul_inv]
  simp only [C6.meanDisc]
  rw [htr, hrotI, disc_fubini hR, disc_scale hR, hvol]
  calc _ = 2 / Real.pi * ‖∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (c * R) s‖ := by
        have hn1 : ‖Complex.exp (Complex.I * ((γ * x₀).re : ℂ))‖ = 1 :=
          Complex.norm_exp_I_mul_ofReal _
        have hn2 : ‖((2 * R ^ 2 : ℝ) : ℂ)‖ = 2 * R ^ 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hn3 : ‖(R ^ 2 * Real.pi)⁻¹‖ = (R ^ 2 * Real.pi)⁻¹ :=
          Real.norm_of_nonneg (by positivity)
        rw [norm_smul, norm_mul, norm_mul, hn1, hn2, hn3]
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        field_simp
    _ ≤ 2 / Real.pi * (10 / (c * R * Real.sqrt (c * R))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 20 / Real.pi * ‖β‖ ^ (-(3 / 2 : ℝ)) * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ)) := by
        rw [hkey]
        ring
end Formalism.FourierDecayAlt.P
