-- Prove2me | solution 5 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:46:49.891128+00:00
-- url     : https://prove2.me/submissions/a1a24abb-7b2a-4d23-b4b7-3a7cd08c53fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by
  obtain ⟨φ, hφ, hroot⟩ := positive_esscher_root_of_unbounded_variation X hnbv q hq
  obtain ⟨ν, m, hνprob, hm, hνcdf, hνlap⟩ :=
    esscher_positive_root_perpetual_infimum_wiener_hopf_scalar X q φ hq hφ hroot
  letI : IsProbabilityMeasure ν := hνprob
  obtain ⟨ν₀, hν₀fin, hν₀supp, hν₀cdf⟩ := chat04_esscher_perpetual_infimum_finite_nonnegative_distribution X φ hφ.le
  letI : IsFiniteMeasure ν₀ := hν₀fin
  have hνeq : ν = ν₀ := by
    apply MeasureTheory.Measure.ext_of_Iic ν ν₀
    intro x
    exact (hνcdf x).trans (hν₀cdf x).symm
  have hνsupp : ν (Iio (0 : ℝ)) = 0 := by simpa [hνeq] using hν₀supp
  let c : ℝ≥0∞ := ENNReal.ofReal m⁻¹
  let β : Measure ℝ := c • ν
  have hcpos : 0 < c := ENNReal.ofReal_pos.mpr (inv_pos.mpr hm)
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβsupp : β (Iio (0 : ℝ)) = 0 := by simp [β, Measure.smul_apply, hνsupp]
  have hβuniv : β univ = c := by simp [β, Measure.smul_apply]
  have hβfin (x : ℝ) : β (Iic x) ≠ ⊤ := by
    have hle : β (Iic x) ≤ c := by
      rw [← hβuniv]
      exact measure_mono (subset_univ _)
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hctop))
  obtain ⟨νp, hνpprob, hνpcdf, hνpbound⟩ :=
    chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
      X q φ hq hφ hroot
  have hβpos (x : ℝ) (hx : 0 < x) : 0 < β (Iic x) := by
    have hreal : 0 < 1 - Real.exp (-(φ / 2) * x) := by
      have : -(φ / 2) * x < 0 := by
        have : 0 < (φ / 2) * x := mul_pos (by linarith) hx
        linarith
      have := Real.exp_lt_one_iff.mpr this
      linarith
    have hνpos : (0 : ℝ≥0∞) < ν (Iic x) := by
      have hle := hνpbound x hx
      rw [hνpcdf x, ← hνcdf x] at hle
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hreal) hle
    change 0 < c * ν (Iic x)
    exact ENNReal.mul_pos hcpos.ne' hνpos.ne'
  have hβlap (s : ℝ) (hs : 0 < s) :
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) =
        ENNReal.ofReal (s / (X.ψ (φ + s) - q)) := by
    have hden : X.ψ (φ + s) - q ≠ 0 := ne_of_gt (sub_pos.mpr
      (levy_psi_root_strictly_above_shift X q φ s hq hφ hs hroot))
    change (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂c • ν) = _
    rw [lintegral_smul_measure, hνlap s hs]
    change ENNReal.ofReal m⁻¹ * ENNReal.ofReal (m * s / (X.ψ (φ + s) - q)) = _
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hm))]
    congr 1
    field_simp [ne_of_gt hm, hden]
  refine ⟨β, φ, 0, hφ, hβfin, hβpos, ?_⟩
  intro θ hθ
  have hψ : q < X.ψ (φ + θ) := levy_psi_root_strictly_above_shift X q φ θ hq hφ hθ hroot
  have hden : X.ψ (φ + θ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hψ)
  have hs0 : 0 ≤ φ + θ := by linarith
  have hWlap := hW.2.2.2.2 (φ + θ) hs0 hψ
  have heqfun : (fun x : ℝ => Real.exp (-θ * x) *
      (Real.exp (-φ * x) * W x)) =
    (fun x : ℝ => Real.exp (-((φ + θ) * x)) * W x) := by
    funext x
    calc
      Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
          (Real.exp (-θ * x) * Real.exp (-φ * x)) * W x := by ring
      _ = Real.exp (-((φ + θ) * x)) * W x := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfInt : IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        (Real.exp (-φ * x) * W x)) (Ioi 0) := by
    simpa only [heqfun] using hWlap.1
  have hWnonneg (x : ℝ) : 0 ≤ W x := by
    by_cases hx : 0 ≤ x
    · exact hW.2.1 x hx
    · rw [hW.1 x (lt_of_not_ge hx)]
  have hfPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => Real.exp (-θ * x) *
        (Real.exp (-φ * x) * W x)) :=
    Filter.Eventually.of_forall
      (fun x => mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (hWnonneg x)))
  have hLin : (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-θ * x) *
        (Real.exp (-φ * x) * W x))) =
      (∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x)) := by
    rw [scaleFunction_tilted_positive_lintegral X q W hW θ φ
        (by simpa [add_comm] using hs0) (by simpa [add_comm] using hψ),
      positiveLaplace_cumulative_measure β θ hθ hβsupp,
      hβlap θ hθ]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / θ : ℝ))]
    congr 1
    simp only [add_comm θ φ]
    field_simp [ne_of_gt hθ, hden]
  obtain ⟨hβInt, hRealEq⟩ := positive_cumulative_laplace_real_integral_bridge
    β hβfin θ (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x))
    hfInt hfPos hLin
  exact ⟨hfInt, hβInt, hRealEq⟩
