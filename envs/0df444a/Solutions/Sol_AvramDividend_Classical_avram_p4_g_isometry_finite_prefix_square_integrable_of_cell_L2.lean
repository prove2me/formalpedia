-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_square_integrable_of_cell_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:07:15.130299+00:00
-- url     : https://prove2.me/submissions/71f7470a-c8c7-41a8-b2c1-043c1b2f77dc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal Nat BigOperators
noncomputable section

/-- A finite sum of L² actual-cell increments has integrable quadratic prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (n : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range n, D i ω) ^ 2) P := by
  have hSum : ∀ k : ℕ,
      MemLp (fun ω => ∑ i ∈ Finset.range k, D i ω) 2 P := by
    intro k
    induction k with
    | zero =>
      convert (MemLp.zero :
        MemLp (fun _ : Ω => (0 : ℝ)) 2 P) using 1
      funext ω
      simp only [Finset.sum_range_zero, Pi.zero_apply]
    | succ k ih =>
      convert ih.add (hD k) using 1
      funext ω
      simp only [Pi.add_apply, Finset.sum_range_succ]
  have hi := (hSum n).integrable_mul (hSum n)
  convert hi using 1
  funext ω
  simp only [Pi.mul_apply, pow_two]
