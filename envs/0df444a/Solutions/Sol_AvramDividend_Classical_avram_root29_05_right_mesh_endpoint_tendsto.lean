-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_right_mesh_endpoint_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:17:47.969324+00:00
-- url     : https://prove2.me/submissions/c1a305e8-082c-4c8d-8f62-229c41f91028

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped BigOperators Classical

/-- The right-hand endpoint of the uniform mesh cell containing a real time
converges to the time itself, a pathwise prerequisite for Fatou's lemma. -/
theorem solution (r : ℝ) :
    Tendsto (fun n : ℕ =>
      ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 r) := by
  let e : ℕ → ℝ := fun n =>
    ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
  have hlow (n : ℕ) : r ≤ e n := by
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hc : r * ((n : ℝ) + 1) ≤
        ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) := Int.le_ceil _
    dsimp [e]
    exact (le_div_iff₀ hp).2 hc
  have hupp (n : ℕ) : e n - r ≤ 1 / ((n : ℝ) + 1) := by
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hc : ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) <
        r * ((n : ℝ) + 1) + 1 := Int.ceil_lt_add_one _
    have hdiv : e n < r + 1 / ((n : ℝ) + 1) := by
      dsimp [e]
      apply (div_lt_iff₀ hp).2
      calc
        _ < r * ((n : ℝ) + 1) + 1 := hc
        _ = (r + 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) := by
          field_simp
    linarith
  have hzero : Tendsto (fun n : ℕ => e n - r) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact sub_nonneg.mpr (hlow n)
    · exact hupp
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := hzero.add_const r
  simpa [e] using h
