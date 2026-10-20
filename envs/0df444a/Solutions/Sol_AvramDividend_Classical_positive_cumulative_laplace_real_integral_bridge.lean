-- Prove2me | solution 1 for AvramDividend.Classical.positive_cumulative_laplace_real_integral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:29:54.979469+00:00
-- url     : https://prove2.me/submissions/831fb144-e198-48b8-a856-2af4d4959cb1

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
A positive-lintegral equality forces the desired real-integral
equality for a finite-valued lower cumulative of a measure.
-/
theorem solution
    (β : Measure ℝ) (hβfin : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (θ : ℝ) (fs : ℝ → ℝ)
    (hfsInt : IntegrableOn fs (Ioi (0 : ℝ)))
    (hfsPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fs)
    (hLap :
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (fs x)) =
      (∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x))) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), fs x) =
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-θ * x) * (β (Iic x)).toReal) := by
  let gb : ℝ → ℝ := fun x =>
    Real.exp (-θ * x) * (β (Iic x)).toReal
  have hcumMono : Monotone (fun x : ℝ => β (Iic x)) := by
    intro x y hxy
    exact measure_mono (Iic_subset_Iic.mpr hxy)
  have hcumMeas : Measurable (fun x : ℝ => (β (Iic x)).toReal) :=
    ENNReal.measurable_toReal.comp hcumMono.measurable
  have hgbMeas : AEStronglyMeasurable gb (volume.restrict (Ioi (0 : ℝ))) := by
    dsimp [gb]
    exact ((by fun_prop : Measurable
      (fun x : ℝ => Real.exp (-θ * x))).mul hcumMeas).aestronglyMeasurable
  have hgbPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] gb := by
    filter_upwards with x
    dsimp [gb]
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hgbLin :
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (gb x)) =
      (∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x)) := by
    apply lintegral_congr
    intro x
    dsimp [gb]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_toReal (hβfin x)]
  have hgbFinite :
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (gb x)) ≠ ⊤ := by
    rw [hgbLin, ← hLap]
    have hfin := ofReal_integral_eq_lintegral_ofReal hfsInt hfsPos
    rw [← hfin]
    exact ENNReal.ofReal_ne_top
  have hgbInt : IntegrableOn gb (Ioi (0 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hgbMeas hgbPos).mp hgbFinite
  have hfsOf := ofReal_integral_eq_lintegral_ofReal hfsInt hfsPos
  have hgbOf := ofReal_integral_eq_lintegral_ofReal hgbInt hgbPos
  have hIntEq :
      (∫ x in Ioi (0 : ℝ), fs x) = ∫ x in Ioi (0 : ℝ), gb x := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg_of_ae hfsPos) (integral_nonneg_of_ae hgbPos)).mp
    rw [hfsOf, hgbOf]
    exact hLap.trans hgbLin.symm
  exact ⟨by simpa [gb] using hgbInt, by simpa [gb] using hIntEq⟩
