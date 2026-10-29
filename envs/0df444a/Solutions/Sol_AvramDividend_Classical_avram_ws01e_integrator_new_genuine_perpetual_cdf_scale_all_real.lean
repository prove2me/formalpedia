-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale_all_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:27:50.955877+00:00
-- url     : https://prove2.me/submissions/ae8e7fc9-1826-469a-b542-c5d0127e5cf8

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
import Theorems.Thm_AvramDividend_Classical_esscher_cumulative_origin_of_finite

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν ∧ 0 < m ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ x : ℝ, ν (Iic x) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x)) := by
  obtain ⟨ν, m, hprob, hm, hcdf, hpos⟩ :=
    AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale X q φ hq hφ hroot W hW
  obtain ⟨ν', -, hν'neg, hcdf', -, -⟩ :=
    AvramDividend.Classical.esscher_positive_root_perpetual_probability_support_laplace X q φ hq hφ hroot
  refine ⟨ν, m, hprob, hm, hcdf, ?_⟩
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [hW.1 x hx, mul_zero, ENNReal.ofReal_zero, hcdf x, ← hcdf' x]
    exact measure_mono_null (Set.Iic_subset_Iio.2 hx) hν'neg
  · have h0 := AvramDividend.Classical.esscher_cumulative_origin_of_finite
      ((ENNReal.ofReal m⁻¹) • ν) φ W
      (fun x => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _))
      ((hW.2.2.1 0 (Set.mem_Ici.2 le_rfl)).mono Set.Ioi_subset_Ici_self)
      (fun x hx => by
        rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hpos x hx,
          ENNReal.toReal_ofReal (inv_nonneg.2 hm.le), ENNReal.toReal_ofReal
            (mul_nonneg (mul_nonneg hm.le (Real.exp_pos _).le) (hW.2.1 x hx.le))]
        field_simp)
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.2 hm.le)] at h0
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one, h0, ← mul_assoc, mul_inv_cancel₀ hm.ne',
      one_mul, ENNReal.ofReal_toReal (measure_ne_top ν _)]
  · exact hpos x hx
