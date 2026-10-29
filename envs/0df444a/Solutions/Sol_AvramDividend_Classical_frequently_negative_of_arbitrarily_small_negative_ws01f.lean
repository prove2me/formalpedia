-- Prove2me | solution 1 for AvramDividend.Classical.frequently_negative_of_arbitrarily_small_negative_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:05:29.673077+00:00
-- url     : https://prove2.me/submissions/b7c2725e-96df-4bbf-981c-0b5a7013702e

import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Topology Set
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ)
    (hzero : f 0 = 0)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ f s < 0) :
    ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0), f t < 0 := by
  let δ : ℕ → ℝ≥0 := fun n =>
    ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hδpos (n : ℕ) : 0 < δ n := by
    apply NNReal.coe_pos.mp
    change (0 : ℝ) < 1 / ((n : ℝ) + 1)
    positivity
  have hδreal :
      Tendsto (fun n : ℕ => (δ n : ℝ)) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0)
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hδzero : Tendsto δ atTop (𝓝 (0 : ℝ≥0)) :=
    (NNReal.tendsto_coe).mp hδreal
  have hChoose (n : ℕ) : ∃ s : ℝ≥0,
      s < δ n ∧ f s < 0 := hsmall (δ n) (hδpos n)
  choose t hlt hneg using hChoose
  have htpos (n : ℕ) : 0 < t n := by
    by_contra hn
    have hz : t n = 0 := le_antisymm (le_of_not_gt hn) bot_le
    have hf : f (t n) = 0 := by simpa [hz] using hzero
    linarith [hneg n]
  have htzero : Tendsto t atTop (𝓝 (0 : ℝ≥0)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hδzero
      (fun n => bot_le) (fun n => (hlt n).le)
  have htwithin : Tendsto t atTop
      (nhdsWithin (0 : ℝ≥0) (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htzero, Filter.Eventually.of_forall htpos⟩
  change ¬ ∀ᶠ s in nhdsWithin (0 : ℝ≥0) (Ioi 0), ¬ f s < 0
  intro hNo
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (htwithin.eventually hNo)
  exact (hN N le_rfl) (hneg N)
