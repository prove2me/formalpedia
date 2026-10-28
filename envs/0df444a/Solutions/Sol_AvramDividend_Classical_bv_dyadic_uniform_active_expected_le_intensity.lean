-- Prove2me | solution 1 for AvramDividend.Classical.bv_dyadic_uniform_active_expected_le_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:11:50.542673+00:00
-- url     : https://prove2.me/submissions/35ffdfac-4645-4907-ad05-4e33ff679175

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_lintegral_active_cell_count
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset
open scoped ENNReal

/-- Equal-mesh active-event probabilities yield a uniform finite-activity expected count bound. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) (N : ℕ) (hN : 0 < N)
    (rate horizon : ℝ)
    (hE : ∀ i : ℕ, i < N → MeasurableSet (E i))
    (hp : ∀ i : ℕ, i < N →
      P.real (E i) =
        1 - Real.exp (-(rate * horizon / (N : ℝ)))) :
    (∫⁻ ω, ∑ i ∈ range N,
      (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) ≤
      ENNReal.ofReal (rate * horizon) := by
  let p : ℝ := 1 - Real.exp (-(rate * horizon / (N : ℝ)))
  have hcast : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hbound : (N : ℝ) * p ≤ rate * horizon := by
    have hh := Real.add_one_le_exp (-(rate * horizon / (N : ℝ)))
    have hp' : p ≤ rate * horizon / (N : ℝ) := by
      dsimp [p]
      linarith
    calc
      (N : ℝ) * p ≤ (N : ℝ) * (rate * horizon / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg N)
      _ = rate * horizon := by field_simp
  have hcell (i : ℕ) (hi : i < N) :
      P (E i) = ENNReal.ofReal p := by
    have hne : P (E i) ≠ ∞ := by finiteness
    calc
      P (E i) = ENNReal.ofReal (P.real (E i)) :=
        (ENNReal.ofReal_toReal hne).symm
      _ = ENNReal.ofReal p := congrArg ENNReal.ofReal (hp i hi)
  calc
    (∫⁻ ω, ∑ i ∈ range N,
      (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) =
      ∑ i ∈ range N, P (E i) :=
        bv_dyadic_lintegral_active_cell_count P E N hE
    _ = ∑ i ∈ range N, ENNReal.ofReal p := by
      apply sum_congr rfl
      intro i hi
      exact hcell i (mem_range.mp hi)
    _ = (N : ℝ≥0∞) * ENNReal.ofReal p := by simp
    _ = ENNReal.ofReal ((N : ℝ) * p) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      simp
    _ ≤ ENNReal.ofReal (rate * horizon) :=
      ENNReal.ofReal_le_ofReal hbound
