-- Prove2me | solution 1 for CohnElkies.exists_plusSaddleSmallRadius_finiteResidue_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/a9574895-10a4-48a5-9a92-955486730326

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadius_weightedCoefficient_error
import Theorems.Thm_CohnElkies_saddleExpSeries_alternating_tail_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ →
          ∀ y : ℝ, 0 ≤ y →
            2 * y ≤ (N : ℝ) + 2 →
              |(∑ n ∈ Finset.range (N + 1),
                  ((-y) ^ n / (n.factorial : ℝ)) *
                    plusSaddleSmallRadiusCoefficient ε ℓ n) -
                Real.exp (-y)| ≤
              (C / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                  (2 * y + y ^ 2) * Real.exp y +
                2 * (y ^ (N + 1) /
                  ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_plusSaddleSmallRadius_weightedCoefficient_error
      hε horder
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ N hN y hy hyratio
  have hmoment := hweight ℓ hℓ N hN y hy
  have htail := saddleExpSeries_alternating_tail_bound
    hy (N + 1) (by
      push_cast
      linarith)
  have hsplit :
      (∑ n ∈ Finset.range (N + 1),
        ((-y) ^ n / (n.factorial : ℝ)) *
          plusSaddleSmallRadiusCoefficient ε ℓ n) =
        (∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)) +
        (∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hcoefficient :
      |∑ n ∈ Finset.range (N + 1),
        ((-y) ^ n / (n.factorial : ℝ)) *
          (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| ≤
      ∑ n ∈ Finset.range (N + 1),
        (y ^ n / (n.factorial : ℝ)) *
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| := by
    calc
      |∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| ≤
        ∑ n ∈ Finset.range (N + 1),
          |((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.range (N + 1),
          (y ^ n / (n.factorial : ℝ)) *
            |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| := by
          apply Finset.sum_congr rfl
          intro n hn
          have hfact : 0 < (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_pos n
          rw [abs_mul, abs_div, abs_pow,
            abs_neg, abs_of_nonneg hy,
            abs_of_pos hfact]
  rw [hsplit]
  calc
    |(∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)) +
        (∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) -
        Real.exp (-y)| =
      |(∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)) +
        ((∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) -
          Real.exp (-y))| := by
        congr 1
        ring
    _ ≤ |∑ n ∈ Finset.range (N + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            (plusSaddleSmallRadiusCoefficient ε ℓ n - 1)| +
        |(∑ n ∈ Finset.range (N + 1),
          (-y) ^ n / (n.factorial : ℝ)) -
          Real.exp (-y)| := abs_add_le _ _
    _ ≤ (∑ n ∈ Finset.range (N + 1),
          (y ^ n / (n.factorial : ℝ)) *
            |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) +
        2 * (y ^ (N + 1) /
          ((N + 1).factorial : ℝ)) := by
        apply add_le_add hcoefficient
        rw [abs_sub_comm]
        exact htail
    _ ≤ (C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp y +
          2 * (y ^ (N + 1) /
            ((N + 1).factorial : ℝ)) :=
        add_le_add hmoment (le_refl _)
end CohnElkies
