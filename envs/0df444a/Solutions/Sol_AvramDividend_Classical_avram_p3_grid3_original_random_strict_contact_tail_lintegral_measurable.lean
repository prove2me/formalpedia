-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:10:02.624995+00:00
-- url     : https://prove2.me/submissions/54417854-f645-451d-b5ec-d053cf83191c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual strict contact cash over a moving measurable interval is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ) (hτ : Measurable τ) (δ : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (τ ω - δ) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by
  classical
  have hRuinM : Measurable (ruinTime X x D) :=
    (ruinTime_stopping_rightCont_filtration X x D hD).measurable'
  let E : Ω → Set ℝ := fun ω =>
    paymentTimes (ruinTime X x D ω) ∩ Ioo (τ ω - δ) (τ ω)
  have hE (ω : Ω) : MeasurableSet (E ω) :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Ioo
  let A : Set (ℝ × Ω) :=
    {p | p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧
      τ p.2 - δ < p.1 ∧ p.1 < τ p.2}
  have hA : MeasurableSet A :=
    (paymentTimes_joint_measurable (ruinTime X x D) hRuinM).inter
      ((measurableSet_lt
        ((hτ.comp measurable_snd).sub measurable_const) measurable_fst).inter
        (measurableSet_lt measurable_fst (hτ.comp measurable_snd)))
  let W : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hW : Measurable W :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_id).neg))
  obtain ⟨κ, hκs, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκs
  have hKernel := measurable_random_indicator_lintegral κ A hA W hW
  have hEq :
      (fun ω : Ω => ∫⁻ t in E ω, W t ∂dividendMeasure D ω) =
      (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ A then W t else 0 ∂κ ω) := by
    funext ω
    rw [hκ ω, ← lintegral_indicator (hE ω) W]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ E ω
    · have htA : (t, ω) ∈ A := ht
      simp [Set.indicator, ht, htA]
    · have htA : (t, ω) ∉ A := fun hs => ht hs
      simp [Set.indicator, ht, htA]
  change Measurable (fun ω : Ω => ∫⁻ t in E ω, W t ∂dividendMeasure D ω)
  rw [hEq]
  simpa only [A, Set.mem_setOf_eq] using hKernel
