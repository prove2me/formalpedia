-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_deficit_mesh_integrability_package
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:44:44.538282+00:00
-- url     : https://prove2.me/submissions/b11aff10-9886-4196-a16b-b350005ab97d

import Mathlib

open MeasureTheory Finset
open scoped BigOperators
theorem S200W_cell {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hm : AEStronglyMeasurable (fun ω => (1 : ℝ) - Real.exp (-c * f ω)) P) :
    Integrable (fun ω => (1 : ℝ) - Real.exp (-c * f ω)) P := by
  refine Integrable.of_bound hm 1 ?_
  filter_upwards [hf] with ω hω
  have h1 : Real.exp (-c * f ω) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : 0 < Real.exp (-c * f ω) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (N : ℕ) (D : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hIncr : ∀ k : ℕ, k < N →
      ∀ᵐ ω ∂P, 0 ≤ D (k + 1) ω - D k ω)
    (hMeas : ∀ k : ℕ, k < N →
      AEStronglyMeasurable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) ∧
    Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P := by
  have hc : 0 ≤ 1 / (2 * a) := by positivity
  have hcell : ∀ k : ℕ, k < N → Integrable
      (fun ω => (1 : ℝ) - Real.exp (-(1 / (2 * a)) * (D (k + 1) ω - D k ω))) P :=
    fun k hk => S200W_cell P (fun ω => D (k + 1) ω - D k ω) _ hc (hIncr k hk) (hMeas k hk)
  refine ⟨hcell, ?_⟩
  refine Integrable.const_mul ?_ _
  refine integrable_finset_sum _ fun k hk => ?_
  have heq : (fun ω => (1 : ℝ) - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a)))) =
      (fun ω => (1 : ℝ) - Real.exp (-(1 / (2 * a)) * (D (k + 1) ω - D k ω))) := by
    funext ω; congr 2; ring
  rw [heq]
  exact hcell k (Finset.mem_range.1 hk)
