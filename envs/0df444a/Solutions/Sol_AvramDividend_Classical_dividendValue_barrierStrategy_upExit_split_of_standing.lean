-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_barrierStrategy_upExit_split_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:44:55.090635+00:00
-- url     : https://prove2.me/submissions/7b4c4c68-2f2a-4ced-b6a5-eec89f04ea6e

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_dividendValue_eq_killed_cantor_expectation
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_first_upExit_discount_coefficient_eq_raw_real
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_sampled_reflected_stopped_reward_killed_factor
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierSupValue_eq_sampled_cantor_expectation
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Genuine reflected-regulator expected dividends split at the strict
successful upcrossing by original-law killed-prefix Strong Markov. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a x : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * dividendValue X q a (barrierStrategy X a a) := by
  let samples : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let mesh : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
  let discount : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
  let weights : ℕ → ℕ → ℝ≥0∞ := fun n k => discount (mesh n (k + 1))
  let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
      if (mesh n (k + 1) : ℝ≥0∞) <
        (⨅ i : ℕ, if f (samples i) - f 0 - (⨆ j : ℕ, if samples j ≤ samples i then
          ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
        then (samples i : ℝ≥0∞) else ⊤) then
        weights n k * ENNReal.ofReal
          ((⨆ j : ℕ, if samples j ≤ mesh n (k + 1) then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal -
           (⨆ j : ℕ, if samples j ≤ mesh n k then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal)
      else 0
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X (a - x)
  let R : Ω → ℝ≥0∞ := ruinTime X x (barrierStrategy X x a)
  have hd : Measurable discount := by
    change Measurable (fun t : ℝ≥0 => ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))))
    fun_prop
  have hValue : dividendValue X q x (barrierStrategy X x a) =
      (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) *
        reward (fun t : ℝ≥0 => X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
        else 0 ∂P) := by
    simpa only [T, R, reward, discount, weights, mesh, samples] using
      avram_root29_05_dividendValue_eq_killed_cantor_expectation X q x a ha hx0 hxa (le_of_lt hq)
  have hMarkov :
      (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) *
        reward (fun t : ℝ≥0 =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
        else 0 ∂P) =
      (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
    simpa only [T, R, reward, discount, weights, mesh, samples] using
      avram_root29_05_sampled_reflected_stopped_reward_killed_factor
        X x a hx0 ha hxa discount hd samples mesh weights
  have hBoundary :
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) =
        dividendValue X q a (barrierStrategy X a a) := by
    have hs := avram_root29_05_barrierSupValue_eq_sampled_cantor_expectation
      X a q (le_of_lt hq)
    change barrierSupValue X a q =
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) at hs
    rw [← hs]
    exact (barrierValue_self_eq_barrierSupValue X q a).symm
  have hDiscount :
      (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) =
      (∫⁻ ω, if (T ω) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * (T ω).toReal))) else 0 ∂P) := by
    simpa only [T, R, discount] using
      avram_root29_05_first_upExit_discount_coefficient_eq_raw_real
        X x a q ha hx0 hxa
  rw [hValue, hMarkov, hBoundary, hDiscount]
  all_goals rfl
