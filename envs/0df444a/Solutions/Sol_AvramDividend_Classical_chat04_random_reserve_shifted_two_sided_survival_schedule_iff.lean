-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_two_sided_survival_schedule_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:07:02.579272+00:00
-- url     : https://prove2.me/submissions/b1d9ac41-b06e-437a-94b9-e93bb307dac3

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_schedule_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Continuous survival inside a two-sided interval equals countable monitoring. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (b + v) ω - X.X b ω) ∧
      H ω + (X.X (b + v) ω - X.X b ω) ≤ a) ↔
    ∀ j : ℕ, τ j ≤ T →
      0 ≤ H ω + (X.X (b + τ j) ω - X.X b ω) ∧
      H ω + (X.X (b + τ j) ω - X.X b ω) ≤ a := by
  have hLower :=
    chat04_random_reserve_shifted_closed_survival_schedule_iff
      X H ω b T τ hCover hTerminal
  have hUpper :=
    chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
      X H ω a b T τ hCover hTerminal
  constructor
  · intro h j hj
    exact ⟨hLower.mp (fun v hv => (h v hv).1) j hj,
      hUpper.mp (fun v hv => (h v hv).2) j hj⟩
  · intro h v hv
    exact ⟨hLower.mpr (fun j hj => (h j hj).1) v hv,
      hUpper.mpr (fun j hj => (h j hj).2) v hv⟩
