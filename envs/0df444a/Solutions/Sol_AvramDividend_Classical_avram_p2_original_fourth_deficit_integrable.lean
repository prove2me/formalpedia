-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_fourth_deficit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:16:13.287332+00:00
-- url     : https://prove2.me/submissions/c6d12e54-7def-4c26-8816-91e35344d40c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Fourth exponential deficit on the original process is integrable,
by expansion into its five genuine nonnegative-rate Laplace moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) :
    Integrable (fun ω => (Real.exp (X.X t ω) - 1) ^ 4) P := by
  have h0 : Integrable (fun ω => Real.exp (0 * X.X t ω)) P :=
    (X.laplace t 0 (le_refl 0)).1
  have h1 : Integrable (fun ω => Real.exp (1 * X.X t ω)) P :=
    (X.laplace t 1 zero_le_one).1
  have h2 : Integrable (fun ω => Real.exp (2 * X.X t ω)) P :=
    (X.laplace t 2 (by norm_num)).1
  have h3 : Integrable (fun ω => Real.exp (3 * X.X t ω)) P :=
    (X.laplace t 3 (by norm_num)).1
  have h4 : Integrable (fun ω => Real.exp (4 * X.X t ω)) P :=
    (X.laplace t 4 (by norm_num)).1
  have hsum : Integrable (fun ω =>
      Real.exp (4 * X.X t ω) -
      4 * Real.exp (3 * X.X t ω) +
      6 * Real.exp (2 * X.X t ω) -
      4 * Real.exp (1 * X.X t ω) +
      Real.exp (0 * X.X t ω)) P :=
    ((((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
      (h1.const_mul 4)).add h0)
  have hpoly (z : ℝ) :
      (Real.exp z - 1) ^ 4 =
        Real.exp (4 * z) - 4 * Real.exp (3 * z) +
        6 * Real.exp (2 * z) - 4 * Real.exp (1 * z) +
        Real.exp (0 * z) := by
    have e2 : Real.exp (2 * z) = Real.exp z ^ 2 := by
      rw [show (2 : ℝ) * z = z + z by ring, Real.exp_add]
      ring
    have e3 : Real.exp (3 * z) = Real.exp z ^ 3 := by
      rw [show (3 : ℝ) * z = (z + z) + z by ring]
      simp only [Real.exp_add]
      ring
    have e4 : Real.exp (4 * z) = Real.exp z ^ 4 := by
      rw [show (4 : ℝ) * z = (z + z) + (z + z) by ring]
      simp only [Real.exp_add]
      ring
    rw [e2, e3, e4]
    simp only [one_mul, zero_mul, Real.exp_zero]
    ring
  have hfun : (fun ω : Ω => (Real.exp (X.X t ω) - 1) ^ 4) =
      (fun ω : Ω =>
        Real.exp (4 * X.X t ω) -
        4 * Real.exp (3 * X.X t ω) +
        6 * Real.exp (2 * X.X t ω) -
        4 * Real.exp (1 * X.X t ω) +
        Real.exp (0 * X.X t ω)) := by
    funext ω
    exact hpoly (X.X t ω)
  rw [hfun]
  exact hsum
