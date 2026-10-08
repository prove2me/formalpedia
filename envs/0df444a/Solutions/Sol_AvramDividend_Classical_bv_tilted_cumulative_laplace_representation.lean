-- Prove2me | solution 1 for AvramDividend.Classical.bv_tilted_cumulative_laplace_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:23:46.209149+00:00
-- url     : https://prove2.me/submissions/88df8ba5-7614-46f5-9f35-13326401c32d

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_fixed_renewal_cumulative_positiveLaplace_canonical
import Theorems.Thm_AvramDividend_Classical_bv_shifted_kernel_gap_on_halfline_canonical
import Theorems.Thm_AvramDividend_Classical_bv_geometric_factor_scale_denominator
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (β : Measure ℝ) (φ b : ℝ), 0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧ 0 < β {0} ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  let φ : ℝ := q / X.drift
  have hφ : 0 < φ := div_pos hq hδ
  obtain ⟨β, bβ, hβfin, hβatom, hβLap⟩ :=
    bv_fixed_renewal_cumulative_positiveLaplace_canonical X hX q hq hbv
  obtain ⟨bg, hbg, hgap⟩ :=
    bv_shifted_kernel_gap_on_halfline_canonical X hX q hq hbv
  let b : ℝ := max bβ (max bg (1 - φ))
  refine ⟨β, φ, b, hφ, hβfin, hβatom, ?_⟩
  intro θ hθb
  have hbβb : bβ ≤ b := le_max_left _ _
  have hbgb : bg ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hthr : 1 - φ ≤ b := le_trans (le_max_right _ _) (le_max_right _ _)
  have hbθ : b ≤ θ := le_of_lt hθb
  have hbβθ : bβ ≤ θ := le_trans hbβb hbθ
  have hbgθ : bg ≤ θ := le_trans hbgb hbθ
  have hθpos : 0 < θ := lt_of_lt_of_le hbg hbgθ
  have hsum1 : 1 ≤ θ + φ := by
    have : 1 - φ < θ := lt_of_le_of_lt hthr hθb
    linarith
  have hgapθ := hgap θ hbgθ
  obtain ⟨hψ, hfactor⟩ :=
    bv_geometric_factor_scale_denominator X hX q hq hbv θ hθpos hsum1 hgapθ
  have hscaleLin : (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal
      (Real.exp (-θ * x) * (Real.exp (-φ * x) * W x))) =
      ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) := by
    simpa [φ] using
      scaleFunction_tilted_positive_lintegral X q W hW θ φ
        (le_trans (by norm_num) hsum1) hψ
  have hβGeom := hβLap θ hbβθ
  have hβLin : (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x)) =
      ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) := by
    rw [hβGeom]
    simpa [φ] using hfactor
  let fs : ℝ → ℝ :=
    fun x => Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)
  let gs : ℝ → ℝ :=
    fun x => Real.exp (-((θ + φ) * x)) * W x
  have hfsgs : fs = gs := by
    funext x
    dsimp [fs, gs]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hWpair := hW.2.2.2.2 (θ + φ)
    (le_trans (by norm_num) hsum1) hψ
  have hfsInt : IntegrableOn fs (Ioi (0 : ℝ)) := by
    rw [hfsgs]
    exact hWpair.1
  have hfsPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fs := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
    dsimp [fs]
    positivity
  let gb : ℝ → ℝ := fun x => Real.exp (-θ * x) * (β (Iic x)).toReal
  have hcumMono : Monotone (fun x : ℝ => β (Iic x)) := by
    intro x y hxy
    exact measure_mono (Iic_subset_Iic.mpr hxy)
  have hcumMeas : Measurable (fun x : ℝ => (β (Iic x)).toReal) :=
    ENNReal.measurable_toReal.comp hcumMono.measurable
  have hgbMeas : AEStronglyMeasurable gb (volume.restrict (Ioi (0 : ℝ))) := by
    dsimp [gb]
    exact ((by fun_prop : Measurable (fun x : ℝ => Real.exp (-θ * x))).mul
      hcumMeas).aestronglyMeasurable
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
    rw [hgbLin, hβLin]
    exact ENNReal.ofReal_ne_top
  have hgbInt : IntegrableOn gb (Ioi (0 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hgbMeas hgbPos).mp hgbFinite
  have hfsOf := ofReal_integral_eq_lintegral_ofReal hfsInt hfsPos
  have hgbOf := ofReal_integral_eq_lintegral_ofReal hgbInt hgbPos
  have hlinEq :
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (fs x)) =
        ∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (gb x) := by
    rw [hgbLin]
    simpa [fs] using hscaleLin.trans hβLin.symm
  have hIntEq :
      (∫ x in Ioi (0 : ℝ), fs x) = ∫ x in Ioi (0 : ℝ), gb x := by
    apply (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg_of_ae hfsPos) (integral_nonneg_of_ae hgbPos)).mp
    rw [hfsOf, hgbOf]
    exact hlinEq
  exact ⟨by simpa [fs] using hfsInt, by simpa [gb] using hgbInt,
    by simpa [fs, gb] using hIntEq⟩
