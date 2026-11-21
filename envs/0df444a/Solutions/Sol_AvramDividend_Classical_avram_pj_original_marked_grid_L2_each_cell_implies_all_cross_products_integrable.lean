-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:09:46.037515+00:00
-- url     : https://prove2.me/submissions/b2d981c9-1986-40e2-aed7-b69bd478ca73

import Mathlib
open MeasureTheory
noncomputable section

/-- Square-integrable original martingale cell increments have
integrable cross products, providing the required finite-grid
off-diagonal expectation well-definedness. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ℕ) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ∈ s, MemLp (Z i) 2 P) :
    ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => Z i ω * Z j ω) P := by
  intro i hi j hj
  exact (hZ i hi).integrable_mul (hZ j hj)
