-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:32:53.908605+00:00
-- url     : https://prove2.me/submissions/a5c46fbd-3a73-458c-90b2-c5fd04a53304

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
/-- Full expected stopped Stieltjes dividends converge along random localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ) (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) =
    ⨆ n, (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) := by
  classical
  let v : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-q * s))
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ), v s ∂dividendMeasure D ω
  have hv : Measurable v := ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
  obtain ⟨κ, hsf, hκ⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : ProbabilityTheory.IsSFiniteKernel κ := hsf
  have hRewardMeas (σ : Ω → ℝ≥0∞) (hσ : Measurable σ) :
      Measurable (fun ω : Ω =>
        ∫⁻ s in paymentTimes (σ ω) ∩ Iic (T : ℝ),
          v s ∂dividendMeasure D ω) := by
    let E : Set (ℝ × Ω) :=
      {p | p.1 ∈ paymentTimes (σ p.2)} ∩ {p | p.1 ∈ Iic (T : ℝ)}
    have hFixed : MeasurableSet {p : ℝ × Ω | p.1 ∈ Iic (T : ℝ)} :=
      measurableSet_Iic.preimage measurable_fst
    have hE : MeasurableSet E :=
      (paymentTimes_joint_measurable σ hσ).inter hFixed
    have hm := measurable_random_indicator_lintegral κ E hE v hv
    convert hm using 1
    funext ω
    rw [hκ ω]
    have hS : MeasurableSet (paymentTimes (σ ω) ∩ Iic (T : ℝ)) :=
      (paymentTimes_measurable (σ ω)).inter measurableSet_Iic
    first
    | simpa only [E, Set.mem_inter_iff, Set.mem_setOf_eq, Set.indicator]
        using (lintegral_indicator hS v)
    | simpa only [E, Set.mem_inter_iff, Set.mem_setOf_eq, Set.indicator]
        using (lintegral_indicator hS v).symm
  have hFm (n : ℕ) : Measurable (F n) := hRewardMeas (τ n) (hτmeas n)
  have hPm : ∀ {a b : ℝ≥0∞}, a ≤ b → paymentTimes a ⊆ paymentTimes b := by
    intro a b hab s hs
    change s ∈ Ici (0 : ℝ) ∩ ({0} ∪ {u : ℝ | ENNReal.ofReal u < a}) at hs
    change s ∈ Ici (0 : ℝ) ∩ ({0} ∪ {u : ℝ | ENNReal.ofReal u < b})
    rcases hs with ⟨hs0, hs | hs⟩
    · exact ⟨hs0, Or.inl hs⟩
    · exact ⟨hs0, Or.inr (lt_of_lt_of_le hs hab)⟩
  have hFmono : Monotone F := by
    intro n m hnm ω; apply lintegral_mono_set
    intro s hs; exact ⟨hPm (hτmono ω hnm) hs.1, hs.2⟩
  have hpoint (ω : Ω) :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        v s ∂dividendMeasure D ω) = ⨆ n, F n ω := by
    rw [← hτsup ω]
    exact avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
      D hD ω T (fun n => τ n ω) (hτmono ω) v hv
  change (∫⁻ ω : Ω, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      v s ∂dividendMeasure D ω) ∂P) =
    ⨆ n, (∫⁻ ω : Ω, F n ω ∂P)
  calc
    _ = (∫⁻ ω : Ω, ⨆ n, F n ω ∂P) := lintegral_congr hpoint
    _ = _ := lintegral_iSup hFm hFmono
