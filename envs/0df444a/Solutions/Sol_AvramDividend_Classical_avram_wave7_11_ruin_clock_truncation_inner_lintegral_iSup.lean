-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:30:07.446412+00:00
-- url     : https://prove2.me/submissions/f3970d20-3ac4-4b7d-a418-f11294d131fd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_nat_horizons
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original Stieltjes payments converge pathwise under increasing natural
    truncations of the genuine ruin clock, including the initial atom. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ⨆ n : ℕ, (∫⁻ t in paymentTimes (min σ (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let S : ℕ → Set ℝ := fun n => paymentTimes (min σ (n : ℝ≥0∞)) ∩ Iic T
  have hSmeas (n : ℕ) : MeasurableSet (S n) :=
    (paymentTimes_measurable _).inter measurableSet_Iic
  have hSmono : Monotone S := by
    intro n m hnm t ht
    have hcast : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hnm
    exact ⟨paymentTimes_min_mono_horizon σ _ _ hcast ht.1, ht.2⟩
  have hUnion : (⋃ n, S n) = paymentTimes σ ∩ Iic T := by
    simpa only [S, Set.iUnion_inter] using
      congrArg (fun s : Set ℝ => s ∩ Iic T)
        (paymentTimes_eq_iUnion_nat_horizons σ).symm
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  let g : ℕ → ℝ → ℝ≥0∞ := fun n t => (S n).indicator f t
  have hgmeas (n : ℕ) : Measurable (g n) := by
    change Measurable ((S n).indicator f)
    exact hf.indicator (hSmeas n)
  have hgmono : Monotone g := by
    intro n m hnm t
    by_cases ht : t ∈ S n
    · have hm : t ∈ S m := hSmono hnm ht
      simp [g, ht, hm]
    · simp [g, ht]
  have hpoint (t : ℝ) :
      (⨆ n, g n t) = (paymentTimes σ ∩ Iic T).indicator f t := by
    by_cases ht : t ∈ paymentTimes σ ∩ Iic T
    · have htunion : t ∈ ⋃ n, S n := hUnion.symm ▸ ht
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp htunion
      apply le_antisymm
      · apply iSup_le
        intro m
        by_cases hm : t ∈ S m
        · simp [g, hm, ht]
        · simp [g, hm, ht]
      · simpa [ht] using
          (le_iSup_of_le n (show f t ≤ g n t by simp [g, hn]))
    · have hnot : ∀ n, t ∉ S n := by
        intro n hn
        exact ht (hUnion ▸ Set.mem_iUnion.mpr ⟨n, hn⟩)
      simp [g, ht, hnot]
  change (∫⁻ t in paymentTimes σ ∩ Iic T, f t ∂μ) =
    ⨆ n, (∫⁻ t in S n, f t ∂μ)
  calc
    (∫⁻ t in paymentTimes σ ∩ Iic T, f t ∂μ) =
        (∫⁻ t, (paymentTimes σ ∩ Iic T).indicator f t ∂μ) :=
      (lintegral_indicator
        ((paymentTimes_measurable σ).inter measurableSet_Iic) f).symm
    _ = (∫⁻ t, ⨆ n, g n t ∂μ) := by
      congr 1
      funext t
      exact (hpoint t).symm
    _ = ⨆ n, (∫⁻ t, g n t ∂μ) := by
      exact lintegral_iSup hgmeas hgmono
    _ = ⨆ n, (∫⁻ t in S n, f t ∂μ) := by
      congr 1
      funext n
      exact lintegral_indicator (hSmeas n) f
