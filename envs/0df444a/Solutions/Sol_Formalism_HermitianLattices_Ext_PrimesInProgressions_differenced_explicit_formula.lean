-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.differenced_explicit_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:52.1249+00:00
-- url     : https://prove2.me/submissions/f1d1c438-954b-49ec-9e88-9270378b151a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharp
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_zero_term
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_log_term
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_arith


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : SharpenS := by
  intro M _ χ Z m K E y δ hZ hy hδ hδ2 hE
  have hy0 : 0 < y := by linarith
  have hEu := hE ((1 + δ) * y) (Or.inr rfl)
  have hEy := hE y (Or.inl rfl)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hEy
  have huy : y < (1 + δ) * y := by nlinarith
  have hR := sharp_arith χ (by linarith : (1 : ℝ) ≤ y) huy
  have hc : y * ((1 + δ) * y) / ((1 + δ) * y - y) = y * ((1 + δ) / δ) := by
    have : (1 + δ) * y - y = δ * y := by ring
    rw [this]; field_simp
  rw [hc] at hR
  set c : ℝ := y * ((1 + δ) / δ) with hcdef
  have hc0 : 0 < c := by positivity
  have hcle : c ≤ 3 / 2 * y / δ := by
    rw [hcdef, show y * ((1 + δ) / δ) = (1 + δ) * y / δ by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  set T : ℂ → ℂ := fun ρ => (c : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ with hT
  have hsum : ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ =
      (c : ℂ) * (∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hT]; ring
  have hTb : ‖∑ ρ ∈ Z, (m ρ : ℂ) * T ρ‖ ≤ 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine norm_sum_le_of_le _ fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_natCast]
    have := sharp_zero_term (hZ ρ hρ).1 (hZ ρ hρ).2 hy0 hδ hδ2
    calc (m ρ : ℝ) * ‖T ρ‖ ≤ (m ρ : ℝ) * (2 * δ * y * y ^ (ρ.re - 1)) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = 2 * δ * y * ((m ρ : ℝ) * y ^ (ρ.re - 1)) := by ring
  have hS0 : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    Finset.sum_nonneg fun ρ _ => by positivity
  have hP : ‖(c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0)‖ ≤ δ * y := by
    by_cases hχ : χ = 1
    · simp only [hχ, if_true]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact sharp_log_term hy0 hδ
    · simp only [hχ, if_false]
      simp; positivity
  have hlog1 : 1 ≤ Real.log (2 * y) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogu : Real.log ((1 + δ) * y) ≤ Real.log (2 * y) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hD : ‖(c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))‖ ≤ c * (2 * E) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hc0.le
    linarith
  have key : psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ =
      (c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))
      - ((c : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y)
      + ((c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0))
      - ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ := by
    rw [hsum]; ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add hD hR)) hP)) hTb).trans ?_
  have b1 : c * (2 * E) ≤ 4 * y * E / δ := by
    calc c * (2 * E) ≤ 3 / 2 * y / δ * (2 * E) := mul_le_mul_of_nonneg_right hcle (by positivity)
      _ = 3 * y * E / δ := by ring
      _ ≤ 4 * y * E / δ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hy0.le hE0]) hδ.le
  have hdy : 0 < δ * y := by positivity
  have b2 : ((1 + δ) * y - y + 1) * Real.log ((1 + δ) * y) ≤ (δ * y + 1) * Real.log (2 * y) := by
    rw [show (1 + δ) * y - y + 1 = δ * y + 1 by ring]
    exact mul_le_mul_of_nonneg_left hlogu (by positivity)
  have b3 : δ * y ≤ (δ * y + 1) * Real.log (2 * y) := by nlinarith
  have b4 : 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) ≤
      20 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS0
  have b5 : 0 ≤ (δ * y + 1) * Real.log (2 * y) := by positivity
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
