-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_cantor_dyadic_drawdown_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T20:25:54.330595+00:00
-- url     : https://prove2.me/submissions/9b9e314c-fc08-49ae-8a60-a56e892bfee6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let r : ℝ≥0 :=
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
      let samples : ℕ → ℝ≥0 := fun j =>
        ((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
      (⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
          (X.X (u + r) ω - X.X u ω))
      atTop (𝓝
        (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
          (X.X (u + t) ω - X.X u ω))) := by
  let round : ℕ → ℝ≥0 := fun n =>
    (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hdense : Dense (Set.range samples) :=
    chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range samples := by
    obtain ⟨j, hj⟩ := chat04_nat_pairing_rational_grid_coverage 1 0 (by decide)
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
  have hround : Tendsto round atTop (𝓝[Set.Ici t] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact dyadic_ceiling_nnreal_tendsto t
    · exact Filter.Eventually.of_forall
        (fun n => dyadic_ceiling_time_ge_nnreal t n)
  have hsup : Tendsto (fun n : ℕ =>
      sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
        Set.Icc 0 (round n))) atTop
      (𝓝 (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
        Set.Icc 0 t))) :=
    (shiftedSup_right_continuous_of_levy X ω u t).tendsto.comp hround
  have hpath : Tendsto (fun n : ℕ => X.X (u + round n) ω - X.X u ω)
      atTop (𝓝 (X.X (u + t) ω - X.X u ω)) :=
    (shiftedLevy_increments_right_continuous X ω u t).tendsto.comp hround
  have hfun : (fun n : ℕ =>
      (⨆ i : ℕ, if samples i ≤ round n then
        ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
          (X.X (u + round n) ω - X.X u ω)) =
      (fun n : ℕ =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
          Set.Icc 0 (round n)) - (X.X (u + round n) ω - X.X u ω)) := by
    funext n
    rw [avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
      X ω u samples hdense hzero (round n) (hround_mem n)]
  change Tendsto (fun n : ℕ =>
    (⨆ i : ℕ, if samples i ≤ round n then
      ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
        (X.X (u + round n) ω - X.X u ω)) atTop
    (𝓝 (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
      (X.X (u + t) ω - X.X u ω)))
  rw [hfun]
  exact hsup.sub hpath
