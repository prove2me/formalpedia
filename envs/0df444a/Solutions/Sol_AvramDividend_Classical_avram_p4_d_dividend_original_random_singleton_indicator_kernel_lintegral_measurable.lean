-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_singleton_indicator_kernel_lintegral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:25:10.060191+00:00
-- url     : https://prove2.me/submissions/c5891b9d-06d7-47ae-a269-8f1b6f338433

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The random time-diagonal singleton integrand is measurable against the
genuine source dividend Stieltjes kernel on path-time pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun p : Ω × ℝ =>
      ∫⁻ s : ℝ, (if s = p.2 then (1 : ℝ≥0∞) else 0) ∂(dividendMeasure D p.1)) := by
  obtain ⟨κ, hκfinite, hκ⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκfinite
  let κ' : Kernel (Ω × ℝ) ℝ := κ.comap Prod.fst measurable_fst
  letI : IsSFiniteKernel κ' := inferInstance
  have hsub : Measurable (fun p : ℝ × (Ω × ℝ) => p.1 - p.2.2) :=
    measurable_fst.sub measurable_snd.snd
  have hdiag : MeasurableSet {p : ℝ × (Ω × ℝ) | p.1 = p.2.2} := by
    have hz : MeasurableSet
        ((fun p : ℝ × (Ω × ℝ) => p.1 - p.2.2) ⁻¹' ({0} : Set ℝ)) :=
      hsub (measurableSet_singleton 0)
    convert hz using 1
    ext p
    simp [sub_eq_zero]
  have hf : Measurable (fun p : ℝ × (Ω × ℝ) =>
      if p.1 = p.2.2 then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite hdiag measurable_const measurable_const
  have hlin : Measurable (fun p : Ω × ℝ =>
      ∫⁻ s : ℝ, (if s = p.2 then (1 : ℝ≥0∞) else 0) ∂κ' p) :=
    Measurable.lintegral_kernel_prod_left (κ := κ') hf
  convert hlin using 1
  funext p
  simp only [κ', Kernel.comap_apply, hκ]
