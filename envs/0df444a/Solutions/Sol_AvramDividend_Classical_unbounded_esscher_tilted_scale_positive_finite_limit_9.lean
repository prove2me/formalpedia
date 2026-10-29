-- Prove2me | solution 9 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:19:02.343545+00:00
-- url     : https://prove2.me/submissions/addb100f-bd96-49e7-9f42-f38ea78fcb5e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
import Theorems.Thm_AvramDividend_Classical_positive_finite_measure_cumulative_converges
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
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  obtain ⟨ν, m, hνP, hm, _, hscale⟩ :=
    avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
      X q φ hq hφ hroot W hW
  letI : IsProbabilityMeasure ν := hνP
  obtain ⟨L, hL, hlim⟩ :=
    positive_finite_measure_cumulative_converges ν
      (by simp) (by simp)
  have hpoint (x : ℝ) (hx : 0 < x) :
      V x = (ν (Iic x)).toReal / m := by
    have hWx : 0 ≤ W x := hW.2.1 x (le_of_lt hx)
    have hpos : 0 ≤ m * Real.exp (-(φ * x)) * W x := by
      positivity
    have hcdf := congrArg ENNReal.toReal (hscale x hx)
    rw [ENNReal.toReal_ofReal hpos] at hcdf
    rw [hV x hx, hcdf]
    field_simp [ne_of_gt hm] <;> ring
  have hEv : V =ᶠ[atTop]
      (fun x : ℝ => (ν (Iic x)).toReal / m) :=
    (eventually_gt_atTop (0 : ℝ)).mono (fun x hx => hpoint x hx)
  refine ⟨L / m, div_pos hL hm, ?_⟩
  exact (hlim.div_const m).congr' hEv.symm
