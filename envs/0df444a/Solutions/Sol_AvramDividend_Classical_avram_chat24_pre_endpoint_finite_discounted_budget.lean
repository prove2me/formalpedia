-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_pre_endpoint_finite_discounted_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:39:00.86901+00:00
-- url     : https://prove2.me/submissions/349ee996-108b-433a-b04b-777b1e84415f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Finite stopped cash budget by discount-weighted telescoping. -/
theorem solution
    (n : ℕ) (e u z d : ℕ → ℝ) (w : ℝ → ℝ)
    (cash err : ℝ)
    (he : ∀ i, i < n → 0 ≤ e (i + 1))
    (hdiv : ∀ i, i < n → d i ≤ w (z i) - w (u (i + 1)))
    (hcash : cash ≤ (∑ i ∈ Finset.range n, e (i + 1) * d i) + err) :
    cash + e n * w (u n) ≤ e 0 * w (u 0) +
      (∑ i ∈ Finset.range n,
        ((e (i + 1) - e i) * w (u i) +
          e (i + 1) * (w (z i) - w (u i)))) + err := by
  let A : ℕ → ℝ := fun i =>
    e (i + 1) * (w (z i) - w (u (i + 1)))
  let B : ℕ → ℝ := fun i =>
    (e (i + 1) - e i) * w (u i) +
      e (i + 1) * (w (z i) - w (u i))
  have htel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, A i) + e k * w (u k) =
        e 0 * w (u 0) + ∑ i ∈ Finset.range k, B i := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        calc
          (∑ i ∈ Finset.range (k + 1), A i) +
              e (k + 1) * w (u (k + 1)) =
            ((∑ i ∈ Finset.range k, A i) +
              e k * w (u k)) + B k := by
                simp only [Finset.sum_range_succ]
                dsimp [A, B]
                ring
          _ = e 0 * w (u 0) + ∑ i ∈ Finset.range (k + 1), B i := by
                rw [ih, Finset.sum_range_succ]
                ring
  have hsum : (∑ i ∈ Finset.range n, e (i + 1) * d i) ≤
      ∑ i ∈ Finset.range n, A i := by
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (hdiv i (Finset.mem_range.mp hi))
      (he i (Finset.mem_range.mp hi))
    simpa only [A] using h
  have htotal := htel n
  dsimp [A, B] at htotal
  linarith
