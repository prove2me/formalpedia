-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T18:22:48.522624+00:00
-- url     : https://prove2.me/submissions/2a455d5e-a748-4f83-9cb0-1da9224d3b06

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_dyadic_ceiling_reflected_drawdown_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let r : ℝ≥0 :=
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
      let samples : ℕ → ℝ≥0 := fun j =>
        ((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
      (⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (X.X (samples i) ω) else 0).toReal - X.X r ω)
      atTop (𝓝 (runningSup X t ω - X.X t ω)) := by
  let round : ℕ → ℝ≥0 := fun n =>
    (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hdense : Dense (Set.range samples) :=
    chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range samples := by
    obtain ⟨j, hj⟩ :=
      chat04_nat_pairing_rational_grid_coverage 1 0 (by decide)
    refine ⟨j, ?_⟩
    simpa [samples] using hj
  have hround_mem (n : ℕ) : round n ∈ Set.range samples := by
    have hn : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
    obtain ⟨j, hj⟩ :=
      chat04_nat_pairing_rational_grid_coverage ((2 : ℕ) ^ n)
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)) hn
    refine ⟨j, ?_⟩
    simpa only [round, samples, div_eq_mul_inv,
      Nat.cast_pow, Nat.cast_ofNat] using hj
  have hEq (n : ℕ) :
      (⨆ i : ℕ, if samples i ≤ round n then
        ENNReal.ofReal (X.X (samples i) ω) else 0).toReal -
          X.X (round n) ω =
      runningSup X (round n) ω - X.X (round n) ω := by
    rw [avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
      X ω samples hdense hzero (round n) (hround_mem n)]
  have hfun :
      (fun n : ℕ =>
        (⨆ i : ℕ, if samples i ≤ round n then
          ENNReal.ofReal (X.X (samples i) ω) else 0).toReal -
            X.X (round n) ω) =
      (fun n : ℕ => runningSup X (round n) ω - X.X (round n) ω) :=
    funext hEq
  change Tendsto (fun n : ℕ =>
    (⨆ i : ℕ, if samples i ≤ round n then
      ENNReal.ofReal (X.X (samples i) ω) else 0).toReal -
        X.X (round n) ω) atTop
    (𝓝 (runningSup X t ω - X.X t ω))
  rw [hfun]
  simpa only [round] using
    avram_ws01e_b_levy_dyadic_ceiling_reflected_drawdown_tendsto X ω t
