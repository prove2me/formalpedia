-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_finite_prefix_memLp_of_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:27:31.097442+00:00
-- url     : https://prove2.me/submissions/3f3b762a-8626-4346-81e8-963673718512

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal Nat BigOperators
noncomputable section

/-- Any finite sum of original L² cell increments is in L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℕ → Ω → ℝ)
    (hD : ∀ i, MemLp (D i) 2 P)
    (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, D i ω) 2 P := by
  induction n with
  | zero =>
    convert (MemLp.zero :
      MemLp (fun _ : Ω => (0 : ℝ)) 2 P) using 1
    funext ω
    simp only [Finset.sum_range_zero, Pi.zero_apply]
  | succ n ih =>
    convert ih.add (hD n) using 1
    funext ω
    simp only [Pi.add_apply, Finset.sum_range_succ]
