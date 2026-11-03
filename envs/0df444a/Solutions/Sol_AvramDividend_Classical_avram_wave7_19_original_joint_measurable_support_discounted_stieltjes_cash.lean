-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:24:51.441127+00:00
-- url     : https://prove2.me/submissions/21e1f8ca-9250-4ba1-b0c2-c0b34a82606e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact original dividendMeasure cash is measurable on any joint random time support. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S) (q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in {t : ℝ | (t, ω) ∈ S},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  classical
  obtain ⟨κ, hκ, heq⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκ
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hf : Measurable f := by dsimp [f]; fun_prop
  let E : Ω → Set ℝ := fun ω => {t : ℝ | (t, ω) ∈ S}
  have hE (ω : Ω) : MeasurableSet (E ω) := by
    exact hS.preimage (measurable_id.prodMk measurable_const)
  have hKernel := measurable_random_indicator_lintegral κ S hS f hf
  have hEq : (fun ω : Ω => ∫⁻ t in E ω, f t ∂(dividendMeasure D ω)) =
      (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ S then f t else 0 ∂κ ω) := by
    funext ω
    rw [heq ω, ← lintegral_indicator (hE ω) f]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ E ω
    · have hs : (t, ω) ∈ S := ht
      simp [Set.indicator, ht, hs]
    · have hs : (t, ω) ∉ S := ht
      simp [Set.indicator, ht, hs]
  change Measurable (fun ω : Ω => ∫⁻ t in E ω, f t ∂(dividendMeasure D ω))
  rw [hEq]
  simpa only [Set.mem_setOf_eq] using hKernel
