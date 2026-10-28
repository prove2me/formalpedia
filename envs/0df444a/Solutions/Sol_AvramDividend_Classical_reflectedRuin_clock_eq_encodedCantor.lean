-- Prove2me | solution 1 for AvramDividend.Classical.reflectedRuin_clock_eq_encodedCantor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:19:45.976139+00:00
-- url     : https://prove2.me/submissions/53e6d332-abb9-4e55-b7f5-155f76d32f97

import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_countableENNReal_record
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The true first reflected ruin time is the strict countable crossing of a Borel encoded record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ,
      if X.X (((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω -
        (⨆ k : ℕ, ENNReal.ofReal
          (if (((Nat.unpair k).2 : ℝ≥0) * (((((Nat.unpair k).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ≤ (((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) then
            max 0 (X.X (((Nat.unpair k).2 : ℝ≥0) * (((((Nat.unpair k).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω) else 0)).toReal < -a
      then ((((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞) else ⊤) := by
  let τ : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  change
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ,
      if X.X (τ j) ω -
        (⨆ k : ℕ, ENNReal.ofReal
          (if τ k ≤ τ j then max 0 (X.X (τ k) ω) else 0)).toReal < -a
      then (τ j : ℝ≥0∞) else ⊤)
  have hdense : Dense (Set.range τ) := by
    simpa only [τ] using chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range τ := by
    obtain ⟨j, hj⟩ := chat04_nat_pairing_rational_grid_coverage 1 0 (by decide)
    refine ⟨j, ?_⟩
    simpa [τ] using hj
  have hclock :
      (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
        (i.1 : ℝ≥0∞)) =
      (⨅ j : ℕ,
        if X.X (τ j) ω - runningSup X (τ j) ω < -a
        then (τ j : ℝ≥0∞) else ⊤) := by
    simpa only [τ, ENNReal.coe_mul] using
      reflectedRuin_strictClock_eq_countableSchedule X ω a
  rw [hclock]
  apply iInf_congr
  intro j
  rw [runningSup_eq_countableENNReal_record X ω τ hdense hzero
    (τ j) ⟨j, rfl⟩]