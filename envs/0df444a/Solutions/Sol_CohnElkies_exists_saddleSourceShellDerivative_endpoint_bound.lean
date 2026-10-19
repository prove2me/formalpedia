-- Prove2me | solution 1 for CohnElkies.exists_saddleSourceShellDerivative_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/c82d2ea7-1713-481e-8f98-3982f0677980

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceShellDerivative_contDiff_one
import Theorems.Thm_CohnElkies_saddleSourceShellDerivative_neg_one

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
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 0,
        |saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε u| ≤
            C * (u + 1) := by
  have hcont :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
        (saddleSourceShellDerivative ε)
        (Icc (-1 : ℝ) 0) := by
    convert! (saddleSourceShellDerivative_contDiff_one
      hε horder).contDiffOn using 1
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound
      (f := saddleSourceShellDerivative ε)
      (n := 0) (by norm_num : (-1 : ℝ) ≤ 0) hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu
  have hbound := hC u hu
  simp only [taylor_within_zero_eval,
    Real.norm_eq_abs, Nat.zero_add, pow_one] at hbound
  rw [saddleSourceShellDerivative_neg_one] at hbound
  have hidentity :
      saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε u =
        saddleSourceShellDerivative ε u -
          -saddleShellDerivativeOne ε := by
    ring
  rw [hidentity]
  calc
    |saddleSourceShellDerivative ε u -
        -saddleShellDerivativeOne ε| ≤
      C * (u - -1) := hbound
    _ ≤ max C 0 * (u + 1) := by
      have hnonneg : 0 ≤ u + 1 := by
        linarith [hu.1]
      calc
        C * (u - -1) = C * (u + 1) := by ring
        _ ≤ max C 0 * (u + 1) :=
          mul_le_mul_of_nonneg_right
            (le_max_left _ _) hnonneg
end CohnElkies
