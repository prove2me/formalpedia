-- Prove2me | solution 1 for CohnElkies.exists_realHyperbolicShellPhase_quadratic_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/415cba74-0589-40cd-9f09-9be99fe90fa3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_contDiff
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_hasDerivAt_one

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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (1 : ℝ) 2,
      |realHyperbolicShellPhase ε x -
          realHyperbolicShellPhase ε 1 -
            (x - 1) * saddleShellDerivativeOne ε| ≤
        C * (x - 1) ^ 2 := by
  have hcont : ContDiffOn ℝ (2 : WithTop ℕ∞)
      (realHyperbolicShellPhase ε) (Set.Icc 1 2) :=
    (realHyperbolicShellPhase_contDiff
      hε horder (2 : WithTop ℕ∞)).contDiffOn
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := realHyperbolicShellPhase ε)
    (n := 1) (by norm_num : (1 : ℝ) ≤ 2) hcont
  have hwithin :
      derivWithin (realHyperbolicShellPhase ε)
        (Set.Icc (1 : ℝ) 2) 1 =
          saddleShellDerivativeOne ε := by
    have hdwithin :
        HasDerivWithinAt (realHyperbolicShellPhase ε)
          (saddleShellDerivativeOne ε)
          (Set.Icc (1 : ℝ) 2) 1 :=
      HasDerivAt.hasDerivWithinAt
        (realHyperbolicShellPhase_hasDerivAt_one hε horder)
    exact HasDerivWithinAt.derivWithin hdwithin
      ((uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2))
        1 (by constructor <;> norm_num))
  have htaylor (x : ℝ) :
      taylorWithinEval (realHyperbolicShellPhase ε)
          1 (Set.Icc (1 : ℝ) 2) 1 x =
        realHyperbolicShellPhase ε 1 +
          (x - 1) * saddleShellDerivativeOne ε := by
    simp [taylorWithinEval_succ, iteratedDerivWithin_one,
      hwithin, smul_eq_mul]
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hxbound := hC x hx
  rw [htaylor x, Real.norm_eq_abs] at hxbound
  calc
    |realHyperbolicShellPhase ε x -
        realHyperbolicShellPhase ε 1 -
          (x - 1) * saddleShellDerivativeOne ε| =
      |realHyperbolicShellPhase ε x -
        (realHyperbolicShellPhase ε 1 +
          (x - 1) * saddleShellDerivativeOne ε)| := by
        congr 1
        ring
    _ ≤ C * (x - 1) ^ 2 := hxbound
    _ ≤ max C 0 * (x - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (le_max_left _ _) (sq_nonneg _)
end CohnElkies
