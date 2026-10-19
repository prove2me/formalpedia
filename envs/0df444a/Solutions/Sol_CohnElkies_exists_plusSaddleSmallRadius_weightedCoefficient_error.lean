-- Prove2me | solution 1 for CohnElkies.exists_plusSaddleSmallRadius_weightedCoefficient_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/a9dea88f-3b62-4637-a18e-11046472a312

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadiusCoefficient_error
import Theorems.Thm_CohnElkies_saddleExpSeries_polynomialMoment_sum_range_le

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
            (∑ n ∈ Finset.range (N + 1),
              (y ^ n / (n.factorial : ℝ)) *
                |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) ≤
              (C / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                  (2 * y + y ^ 2) * Real.exp y := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_plusSaddleSmallRadiusCoefficient_error hε horder
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ N hN y hy
  have hnonneg : 0 ≤ (C / ℓ) *
      Real.exp (C * (N : ℝ) ^ 2 / ℓ) := by
    positivity
  calc
    (∑ n ∈ Finset.range (N + 1),
        (y ^ n / (n.factorial : ℝ)) *
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1|) ≤
      ∑ n ∈ Finset.range (N + 1),
        ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
          (((n : ℝ) + (n : ℝ) ^ 2) *
            (y ^ n / (n.factorial : ℝ))) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n ≤ N :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        have hnNreal : (n : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hnN
        have hnpole : 2 * (n : ℝ) ≤ ℓ :=
          (mul_le_mul_of_nonneg_left hnNreal (by norm_num)).trans hN
        have hbound := hcoeff ℓ hℓ n hnpole
        have hterm : 0 ≤ y ^ n / (n.factorial : ℝ) := by
          positivity
        have hq :
            C * (n : ℝ) ^ 2 / ℓ ≤
              C * (N : ℝ) ^ 2 / ℓ := by
          gcongr
        have hbase :
            0 ≤ C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
          positivity
        calc
          (y ^ n / (n.factorial : ℝ)) *
              |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
            (y ^ n / (n.factorial : ℝ)) *
              ((C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
                Real.exp (C * (n : ℝ) ^ 2 / ℓ)) :=
              mul_le_mul_of_nonneg_left hbound hterm
          _ ≤ (y ^ n / (n.factorial : ℝ)) *
              ((C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
                Real.exp (C * (N : ℝ) ^ 2 / ℓ)) := by
              gcongr
          _ = ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
              (((n : ℝ) + (n : ℝ) ^ 2) *
                (y ^ n / (n.factorial : ℝ))) := by
              ring
    _ = ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
        (∑ n ∈ Finset.range (N + 1),
          ((n : ℝ) + (n : ℝ) ^ 2) *
            (y ^ n / (n.factorial : ℝ))) := by
          rw [Finset.mul_sum]
    _ ≤ ((C / ℓ) * Real.exp (C * (N : ℝ) ^ 2 / ℓ)) *
        ((2 * y + y ^ 2) * Real.exp y) :=
          mul_le_mul_of_nonneg_left
            (saddleExpSeries_polynomialMoment_sum_range_le
              hy (N + 1)) hnonneg
    _ = (C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp y := by ring
end CohnElkies
