-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_mixed_commutator_eq_w_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:11:33.614965+00:00
-- url     : https://prove2.me/submissions/127eb3b1-64f6-439b-abc8-110aed067163

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The physical original cap-linear mixed drift/J commutator
is exactly the true w commutator on any cap-safe drift-upshift grid.
Raw negative jump mass is source-proved nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal)
    (hUp : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal) :
    let V : ℝ → ℝ := fun r =>
      if C = ⊤ then w r else if r ≤ C.toReal then w r
      else w C.toReal + (r - C.toReal)
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i =>
      (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (V (z i + c i - j i) - V (z i + c i) -
        V (z i - j i) + V (z i))) =
    (∑ i ∈ Finset.range n,
      e i * (w (z i + c i - j i) - w (z i + c i) -
        w (z i - j i) + w (z i))) := by
  intro V z c j e
  apply Finset.sum_congr rfl
  intro i hi
  have hJ := avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
    X ω (u i) (u (i + 1)) (hu (Nat.le_succ i))
  have hEq := avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap
    w C (z i) (c i) (j i)
    (by simpa only [z] using hCap i (Finset.mem_range.mp hi))
    (by simpa only [z, c] using hUp i (Finset.mem_range.mp hi))
    (by simpa only [j] using hJ)
  simpa only [V] using congrArg (fun r : ℝ => e i * r) hEq
