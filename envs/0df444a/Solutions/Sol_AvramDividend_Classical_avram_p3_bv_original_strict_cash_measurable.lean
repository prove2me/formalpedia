-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:10:39.717134+00:00
-- url     : https://prove2.me/submissions/ee2f688c-0dd5-4443-8882-8cb7a1ded5fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true stopped Stieltjes payment strictly before T is measurable,
including the time-zero right-payment and excluding the horizon atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (hσ : Measurable σ)
    (q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  classical
  obtain ⟨κ, hκ, heq⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκ
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hf : Measurable f := by dsimp [f]; fun_prop
  let E : Ω → Set ℝ := fun ω => paymentTimes (σ ω) ∩ Iio T
  let S : Set (ℝ × Ω) := {p | p.1 ∈ paymentTimes (σ p.2) ∩ Iio T}
  have hE (ω : Ω) : MeasurableSet (E ω) := by
    dsimp [E, paymentTimes]; measurability
  have hS : MeasurableSet S := by
    have hEq : S =
        {p : ℝ × Ω | p.1 ∈ paymentTimes (σ p.2)} ∩
        {p : ℝ × Ω | p.1 ∈ Iio T} := by
      ext p; simp only [S, mem_setOf_eq, mem_inter_iff]
    rw [hEq]
    exact (paymentTimes_joint_measurable σ hσ).inter
      (measurableSet_Iio.preimage measurable_fst)
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
  simpa only [S, Set.mem_setOf_eq] using hKernel
