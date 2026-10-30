-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:13:24.082547+00:00
-- url     : https://prove2.me/submissions/b18ad16f-6119-4232-a9ec-e548e8862b24

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The actual stopped running-supremum Stieltjes reward equals the measurable
countable Cantor-sampled reflected dividend reward on every original Lévy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a q : ℝ) (hq : 0 ≤ q) :
    (let τ : ℝ≥0∞ :=
       ⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
         (i.1 : ℝ≥0∞)
     ∫⁻ r in paymentTimes τ,
       if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
         ∂(dividendMeasure (runningSup X) ω)) =
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let record : ℝ≥0 → ℝ := fun t =>
       (⨆ j : ℕ,
         if samples j ≤ t then
           ENNReal.ofReal (X.X (samples j) ω - X.X 0 ω) else 0).toReal
     let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
       (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ i : ℕ,
       if X.X (samples i) ω - X.X 0 ω - record (samples i) < -a
       then (samples i : ℝ≥0∞) else ⊤
     ⨆ n : ℕ, ⨆ N : ℕ,
       ∑ k ∈ Finset.range N,
         if (grid n (k + 1) : ℝ≥0∞) < ρ then
           ENNReal.ofReal
             (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
           ENNReal.ofReal
             (record (grid n (k + 1)) - record (grid n k))
         else 0) := by
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let record : ℝ≥0 → ℝ := fun t =>
    (⨆ j : ℕ, if samples j ≤ t then
      ENNReal.ofReal (X.X (samples j) ω - X.X 0 ω) else 0).toReal
  let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
    (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
  let τ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
    (i.1 : ℝ≥0∞)
  let ρ : ℝ≥0∞ := ⨅ i : ℕ,
    if X.X (samples i) ω - X.X 0 ω - record (samples i) < -a
    then (samples i : ℝ≥0∞) else ⊤
  have hclock : τ = ρ := by
    simpa [τ, ρ, record, samples] using
      avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock X ω a
  have hrecord (n k : ℕ) :
      record (grid n k) = runningSup X (grid n k) ω := by
    simpa [record, grid, samples] using
      (avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid
        X ω (n + 1) k (Nat.succ_pos n))
  change (∫⁻ r in paymentTimes τ,
    if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) =
    ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
      if (grid n (k + 1) : ℝ≥0∞) < ρ then
        ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
          ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k))
      else 0
  rw [avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup X ω τ q hq,
      hclock]
  apply iSup_congr
  intro n
  apply iSup_congr
  intro N
  apply Finset.sum_congr rfl
  intro k hk
  simp only [grid, ← NNReal.coe_mul, Real.toNNReal_coe,
    ENNReal.ofReal_coe_nnreal, ← hrecord n (k + 1), ← hrecord n k]
