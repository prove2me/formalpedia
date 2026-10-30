-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_sampled_reflected_stopped_reward_killed_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:59:11.112611+00:00
-- url     : https://prove2.me/submissions/f53a5d75-28a5-4fb3-b8c2-3e5fb2fcbe2a

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_path_countable_reflected_stopped_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_uncapped_barrier_killed_future_reward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- For the actual original-barrier killed first passage, the complete sampled,
stopped Stieltjes-record reward satisfies the uncapped Strong-Markov factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (samples : ℕ → ℝ≥0) (mesh : ℕ → ℕ → ℝ≥0)
    (weights : ℕ → ℕ → ℝ≥0∞) :
    let sampledReward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
      ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
        if (mesh n (k + 1) : ℝ≥0∞) <
          (⨅ i : ℕ,
            if f (samples i) - f 0 -
              (⨆ j : ℕ,
                if samples j ≤ samples i then
                  ENNReal.ofReal (f (samples j) - f 0)
                else 0).toReal < -a then
              (samples i : ℝ≥0∞)
            else ⊤) then
          weights n k * ENNReal.ofReal
            ((⨆ i : ℕ,
                if samples i ≤ mesh n (k + 1) then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal -
              (⨆ i : ℕ,
                if samples i ≤ mesh n k then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal)
        else 0
    let T := twoSidedExitUpTime X (a - x)
    let R := ruinTime X x (barrierStrategy X x a)
    (∫⁻ ω, if T ω < R ω then
      discount ((T ω).toNNReal) *
        sampledReward (fun t : ℝ≥0 =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
      else 0 ∂P) =
    (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
      (∫⁻ ω, sampledReward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  exact avram_root29_05_uncapped_barrier_killed_future_reward_factor
    X x a hx ha hxa discount hd
    _ (path_countable_reflected_stopped_reward_measurable samples mesh weights a)
