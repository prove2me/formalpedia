-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_expected_preruin_locally_joint_measurable_stieltjes_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:36:14.984278+00:00
-- url     : https://prove2.me/submissions/22d3bf6d-cebe-4e37-8049-5c26a0b5b5ea

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_stieltjes_reward_localisation_supremum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (f : ℝ × Ω → ℝ≥0∞)
    (hfpath : ∀ ω, Measurable (fun s : ℝ => f (s, ω)))
    (hfmask : ∀ n, Measurable (fun p : ℝ × Ω =>
      if p.1 ∈ paymentTimes (τ n p.2) ∩ Iic (T : ℝ) then f p else 0)) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω ∂P) =
    ⨆ n, (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω ∂P) := by
  classical
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ), f (s, ω) ∂dividendMeasure D ω
  obtain ⟨κ, hsf, hκ⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : ProbabilityTheory.IsSFiniteKernel κ := hsf
  have hFm (n : ℕ) : Measurable (F n) := by
    let E : Set (ℝ × Ω) :=
      {p | p.1 ∈ paymentTimes (τ n p.2) ∩ Iic (T : ℝ)}
    have hUncurry : Measurable (Function.uncurry
        (fun s ω => if (s, ω) ∈ E then f (s, ω) else 0)) := by
      convert hfmask n using 1
      funext p
      rcases p with ⟨s, ω⟩
      rfl
    have hm : Measurable (fun ω : Ω =>
        ∫⁻ s, if (s, ω) ∈ E then f (s, ω) else 0 ∂κ ω) :=
      Measurable.lintegral_kernel_prod_left
        (κ := κ) (f := fun s ω => if (s, ω) ∈ E then f (s, ω) else 0)
        hUncurry
    convert hm using 1
    funext ω
    rw [hκ ω]
    have hS : MeasurableSet (paymentTimes (τ n ω) ∩ Iic (T : ℝ)) :=
      (paymentTimes_measurable (τ n ω)).inter measurableSet_Iic
    first
    | simpa only [E, Set.mem_setOf_eq, Set.indicator]
        using (lintegral_indicator hS (fun s => f (s, ω)))
    | simpa only [E, Set.mem_setOf_eq, Set.indicator]
        using (lintegral_indicator hS (fun s => f (s, ω))).symm
  have hPm : ∀ {a b : ℝ≥0∞}, a ≤ b → paymentTimes a ⊆ paymentTimes b := by
    intro a b hab s hs
    change s ∈ Ici (0 : ℝ) ∩ ({0} ∪ {u : ℝ | ENNReal.ofReal u < a}) at hs
    change s ∈ Ici (0 : ℝ) ∩ ({0} ∪ {u : ℝ | ENNReal.ofReal u < b})
    rcases hs with ⟨hs0, hs | hs⟩
    · exact ⟨hs0, Or.inl hs⟩
    · exact ⟨hs0, Or.inr (lt_of_lt_of_le hs hab)⟩
  have hFmono : Monotone F := by
    intro n m hnm ω
    apply lintegral_mono_set
    intro s hs
    exact ⟨hPm (hτmono ω hnm) hs.1, hs.2⟩
  have hpoint (ω : Ω) :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        f (s, ω) ∂dividendMeasure D ω) = ⨆ n, F n ω := by
    rw [← hτsup ω]
    exact avram_wave4_04b_complete_stieltjes_reward_localisation_supremum
      D hD ω T (fun n => τ n ω) (hτmono ω) (fun s => f (s, ω)) (hfpath ω)
  change (∫⁻ ω : Ω, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      f (s, ω) ∂dividendMeasure D ω) ∂P) =
    ⨆ n, (∫⁻ ω : Ω, F n ω ∂P)
  calc
    _ = (∫⁻ ω : Ω, ⨆ n, F n ω ∂P) := lintegral_congr hpoint
    _ = _ := lintegral_iSup hFm hFmono
