-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_contact_tail_sets_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:43:17.898196+00:00
-- url     : https://prove2.me/submissions/40421835-ff52-492d-9b93-96e84b04aa85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped payment-time tail sets form an antitone sequence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    Antitone (fun m : ℕ =>
      paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ)) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  change Antitone (fun m : ℕ =>
    paymentTimes (ruinTime X x D ω) ∩
      Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ))
  intro i j hij
  have hDen : ((i + 1 : ℕ) : ℝ≥0) ≤ ((j + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.add_le_add_right hij 1
  have hDel : T / ((j + 1 : ℕ) : ℝ≥0) ≤
      T / ((i + 1 : ℕ) : ℝ≥0) := by
    gcongr
  have hFloor :
      τ - T / ((i + 1 : ℕ) : ℝ≥0) ≤
      τ - T / ((j + 1 : ℕ) : ℝ≥0) :=
    tsub_le_tsub_left hDel τ
  have hFloorReal :
      ((τ - T / ((i + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) ≤
      ((τ - T / ((j + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
    exact_mod_cast hFloor
  have hFloorReal' :
      ((τ - T / (i + 1) : ℝ≥0) : ℝ) ≤
      ((τ - T / (j + 1) : ℝ≥0) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hFloorReal
  intro s hs
  exact ⟨hs.1, ⟨lt_of_le_of_lt hFloorReal' hs.2.1, hs.2.2⟩⟩
