-- Prove2me | solution 1 for FourierJacobi.Analysis.finiteRegular_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:40.76052+00:00
-- url     : https://prove2.me/submissions/d6a1aaa4-be89-4686-bead-f6f62a34b45f

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_GeometricRange_regionRegular
import Theorems.Thm_FourierJacobi_Analysis_geometricRange_undamped
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_unitary
import Theorems.Thm_FourierJacobi_Algebra_weyl_common_euler_factorization
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution {t : ℝ} {a b d : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : t < ‖d‖) (hdhi : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    FiniteRegular (t : ℂ) a b d := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  have hdpos : 0 < ‖d‖ := lt_trans ht₀ hdlo
  have hd₀ : d ≠ 0 := norm_pos_iff.mp hdpos
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht₀]
  have hdt : ‖d * (t : ℂ)‖ < 1 := by
    rw [norm_mul, htn]
    nlinarith
  have htd : ‖(t : ℂ) / d‖ < 1 := by
    rw [norm_div, htn]
    exact (div_lt_one hdpos).mpr hdlo
  have hD₁ : d₁ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb hdt
  have hD₂ : d₂ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb htd
  have hWall : weylWall a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr ha₁)
      (sub_ne_zero.mpr hab)) (sub_ne_zero.mpr hb₁)) (sub_ne_zero.mpr hab₁)
  refine ⟨ha₀, hb₀, hd₀, sub_ne_zero.mpr ha₁, sub_ne_zero.mpr hb₁,
    sub_ne_zero.mpr hab, sub_ne_zero.mpr hab₁, ?_, ?_⟩
  · rw [weyl_common_euler_factorization (t : ℂ) a b d ha₀ hb₀ hd₀]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hWall
        (pow_ne_zero 2 ha₀)) (pow_ne_zero 2 hb₀)) hd₀)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) (pow_ne_zero 2 hb₀))
          (pow_ne_zero 4 hd₀)))
      (mul_ne_zero hD₁ hD₂)
  · intro i
    have hr := (geometricRange_undamped ht₀ ht₁ hdlo hdhi
      (weylU_unitary ha hb i) (weylV_unitary ha hb i)).regionRegular
    simpa only [one_mul] using hr
end FourierJacobi.Analysis
