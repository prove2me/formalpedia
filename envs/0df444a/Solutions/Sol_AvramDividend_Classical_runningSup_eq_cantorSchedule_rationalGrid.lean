-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_eq_cantorSchedule_rationalGrid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:44:31.184622+00:00
-- url     : https://prove2.me/submissions/aa5a82d2-6606-441b-bb24-0e3b9d7bba7e

import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_onSample
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full regulator at each rational payment-grid endpoint is its scheduled path supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n k : ℕ) (hn : 0 < n) :
    runningSup X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω =
      ⨆ s : {s : ℝ≥0 //
        s ∈ Set.range (fun j : ℕ =>
          ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ∧
        s ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹}, X.X s.1 ω := by
  let τ : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let S : Set ℝ≥0 := Set.range τ
  have hDense : Dense S := chat05_cantor_rational_schedule_dense
  have h0 : (0 : ℝ≥0) ∈ S := by
    obtain ⟨j, hj⟩ :=
      chat04_nat_pairing_rational_grid_coverage 1 0 (by decide)
    change ∃ i : ℕ, τ i = 0
    refine ⟨j, ?_⟩
    simpa [τ] using hj
  have ht : ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ∈ S := by
    change ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹
    exact chat04_nat_pairing_rational_grid_coverage n k hn
  exact runningSup_eq_densePrefix_onSample X S hDense h0 _ ht ω
