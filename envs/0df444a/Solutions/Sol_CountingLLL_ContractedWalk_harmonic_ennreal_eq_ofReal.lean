-- Prove2me | solution 1 for CountingLLL.ContractedWalk.harmonic_ennreal_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:10:58.713417+00:00
-- url     : https://prove2.me/submissions/80cbef88-f1c3-4553-8e4d-731bfc64df40

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

/-- A finite harmonic expectation, with real and extended-nonnegative conventions. -/
theorem solution {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) (hKi : Integrable (fun x => (K x : ℝ)) ν) :
    (∫⁻ x, ∑ k ∈ Finset.range (K x), (((k+2 : ℕ) : ℝ≥0∞)⁻¹) ∂ν) =
      ENNReal.ofReal (∫ x, ∑ k ∈ Finset.range (K x), (1:ℝ)/(k+2) ∂ν) := by
  classical
  let H : β → ℝ := fun x => ∑ k ∈ Finset.range (K x), (1:ℝ)/(k+2)
  have hHm : Measurable H := by
    let Hnat : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, (1:ℝ)/(k+2)
    exact (measurable_of_countable Hnat).comp hK
  have hH0 : ∀ x, 0 ≤ H x := by
    intro x
    exact Finset.sum_nonneg (fun k hk => by positivity)
  have hH1 : ∀ x, H x ≤ (K x : ℝ) := by
    intro x
    calc
      _ ≤ ∑ _k ∈ Finset.range (K x), (1:ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply (div_le_one₀ (by positivity)).2
        have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith
      _ = (K x : ℝ) := by simp
  have hHi : Integrable H ν := by
    apply hKi.mono' hHm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hH0 x)]
    exact hH1 x
  rw [ofReal_integral_eq_lintegral_ofReal hHi (Filter.Eventually.of_forall hH0)]
  apply lintegral_congr
  intro x
  change (∑ k ∈ Finset.range (K x), (((k+2 : ℕ) : ℝ≥0∞)⁻¹)) = ENNReal.ofReal (∑ k ∈ Finset.range (K x), (1:ℝ)/(k+2))
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => by positivity)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < (k:ℝ)+2)]
  simp [ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ (k:ℝ))]
