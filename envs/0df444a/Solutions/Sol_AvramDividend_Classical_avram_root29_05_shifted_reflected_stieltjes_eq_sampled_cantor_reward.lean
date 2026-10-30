-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:20:46.057309+00:00
-- url     : https://prove2.me/submissions/b7f47390-3c76-477c-8942-b4ad39f57b35

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Actual strictly killed future Lévy regulator Stieltjes cash matches the
same globally measurable Cantor-sampled future-path reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (age : ℝ≥0) (a q : ℝ) (hq : 0 ≤ q) :
    (let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     let τ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)
     ∫⁻ r in paymentTimes τ, if 0 < r then
       ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (fun t (_ : Ω) => M t) ω)) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
     let samples : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let record : ℝ≥0 → ℝ := fun t => (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
     let grid : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a then (samples i : ℝ≥0∞) else ⊤
     ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
       if (grid n (k + 1) : ℝ≥0∞) < ρ then ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
         ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0) := by
  let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
  let M : ℝ≥0 → ℝ := fun t => sSup (f '' Icc 0 t)
  let samples : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let record : ℝ≥0 → ℝ := fun t => (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
  let grid : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
  let τ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)
  let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a then (samples i : ℝ≥0∞) else ⊤
  have hdense : Dense (Set.range samples) := by
    simpa [samples] using chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range samples := by
    refine ⟨Nat.pair 0 0, ?_⟩
    simp [samples]
  have hrec (j : ℕ) : record (samples j) = M (samples j) := by
    simpa [record, f, M] using
      (avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
        X ω age samples hdense hzero (samples j) ⟨j, rfl⟩)
  have hclock : τ = ρ := by
    have hs : τ = (⨅ j : ℕ,
        if f (samples j) - M (samples j) < -a
        then (samples j : ℝ≥0∞) else ⊤) := by
      simpa [τ, samples, f, M] using
        (avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule X ω age a)
    rw [hs]
    apply iInf_congr
    intro j
    rw [← hrec j]
    have hf0 : f 0 = 0 := by simp [f]
    simp only [ρ, hf0, sub_zero]
  have hrecord (n k : ℕ) : record (grid n k) = M (grid n k) := by
    simpa [record, f, M, grid, samples] using
      (avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
        X ω age (n + 1) k (Nat.succ_pos n))
  change (∫⁻ r in paymentTimes τ, if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
    ∂(dividendMeasure (fun t (_ : Ω) => M t) ω)) =
    ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
      if (grid n (k + 1) : ℝ≥0∞) < ρ then ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
        ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0
  rw [avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup X ω age τ q hq, hclock]
  apply iSup_congr
  intro n
  apply iSup_congr
  intro N
  apply Finset.sum_congr rfl
  intro k hk
  rw [hrecord n (k + 1), hrecord n k]
  simp only [grid, ← NNReal.coe_mul, Real.toNNReal_coe, ENNReal.ofReal_coe_nnreal]
  rfl
