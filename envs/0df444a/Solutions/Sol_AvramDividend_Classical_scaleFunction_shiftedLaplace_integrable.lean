-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_shiftedLaplace_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:35:58.625433+00:00
-- url     : https://prove2.me/submissions/1890dad9-6e3a-46ea-b1ac-187b101ff298

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x + y))
      (Ioi (0 : ℝ)) := by
  have hmono : Monotone W := by
    intro u v huv
    by_cases hv : v < 0
    · have hu : u < 0 := lt_of_le_of_lt huv hv
      rw [hW.1 u hu, hW.1 v hv]
    · have hv0 : 0 ≤ v := le_of_not_gt hv
      by_cases hu : u < 0
      · rw [hW.1 u hu]
        exact hW.2.1 v hv0
      · exact hW.2.2.2.1 (le_of_not_gt hu) hv0 huv
  have hmeasW : Measurable W := hmono.measurable
  have hmeasShift : Measurable (fun x : ℝ => W (x + y)) :=
    hmeasW.comp (measurable_id.add measurable_const)
  have hmeasExp : Measurable (fun x : ℝ => Real.exp (-(θ * x))) := by
    fun_prop
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => Real.exp (-(θ * x)) * W (x + y))
        (volume.restrict (Ioi (0 : ℝ))) :=
    (hmeasExp.mul hmeasShift).aestronglyMeasurable
  have hbase : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) := (hW.2.2.2.2 θ hθ hqθ).1
  apply hbase.mono' hmeas
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (μ := (volume : Measure ℝ)) measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_of_lt hx
  have hWxy : 0 ≤ W (x + y) := by
    by_cases hneg : x + y < 0
    · rw [hW.1 (x + y) hneg]
    · exact hW.2.1 (x + y) (le_of_not_gt hneg)
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hle : W (x + y) ≤ W x := hmono (by linarith)
  simp only [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_nonneg _) hWxy),
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hWx)]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)
