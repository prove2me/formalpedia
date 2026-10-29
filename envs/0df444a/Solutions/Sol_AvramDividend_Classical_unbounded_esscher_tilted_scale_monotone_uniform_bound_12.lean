-- Prove2me | solution 12 for AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:20:51.89117+00:00
-- url     : https://prove2.me/submissions/c46e9d87-ac90-46c2-957f-052da8028dc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    MonotoneOn V (Ioi (0 : ℝ)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by
  obtain ⟨ν, m, hνP, hm, _, hscale⟩ :=
    avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
      X q φ hq hφ hroot W hW
  letI : IsProbabilityMeasure ν := hνP
  have hpoint (x : ℝ) (hx : 0 < x) :
      V x = (ν (Iic x)).toReal / m := by
    have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
    have hpos : 0 ≤ m * Real.exp (-(φ * x)) * W x := by
      positivity
    have hcdf := congrArg ENNReal.toReal (hscale x hx)
    rw [ENNReal.toReal_ofReal hpos] at hcdf
    rw [hV x hx, hcdf]
    field_simp [ne_of_gt hm] <;> ring
  refine ⟨?_, ⟨(ν univ).toReal / m, ?_⟩⟩
  · intro x hx y hy hxy
    rw [hpoint x hx, hpoint y hy]
    have hle : ν (Iic x) ≤ ν (Iic y) :=
      measure_mono (Iic_subset_Iic.mpr hxy)
    exact div_le_div_of_nonneg_right
      (ENNReal.toReal_mono (measure_ne_top ν (Iic y)) hle) hm.le
  · intro x hx
    rw [hpoint x hx]
    have hle : ν (Iic x) ≤ ν univ :=
      measure_mono (subset_univ _)
    exact div_le_div_of_nonneg_right
      (ENNReal.toReal_mono (measure_ne_top ν univ) hle) hm.le
