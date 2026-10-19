-- Prove2me | solution 1 for CohnElkies.plusSaddleSmallRadiusCoefficient_error_of_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/96d7a25b-d6b5-498b-bf95-6fd3461177bf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddleSmallRadiusPolynomial_error
import Theorems.Thm_CohnElkies_abs_exp_sub_one_le_abs_mul_exp_abs

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
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ)
    (C : ℝ) (hC : 0 ≤ C)
    (hphase :
      |ℓ *
          (realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ) -
              realHyperbolicShellPhase ε 1) -
          2 * (n : ℝ) * saddleShellDerivativeOne ε| ≤
        C * (n : ℝ) ^ 2 / ℓ) :
    |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
      (C * (n : ℝ) ^ 2 / ℓ +
        (18 / beta ε) * ((n : ℝ) / ℓ)) *
          Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
  let E : ℝ :=
    ℓ * (realHyperbolicShellPhase ε
      (1 + 2 * (n : ℝ) / ℓ) -
        realHyperbolicShellPhase ε 1) -
      2 * (n : ℝ) * saddleShellDerivativeOne ε
  let P : ℝ :=
    (beta ε - (2 * (n : ℝ) / ℓ) *
      (2 + 2 * (n : ℝ) / ℓ) ^ 2) / beta ε
  let q : ℝ := C * (n : ℝ) ^ 2 / ℓ
  let k : ℝ := (18 / beta ε) * ((n : ℝ) / ℓ)
  have hq : 0 ≤ q := by
    try dsimp [q]
    positivity
  have hk : 0 ≤ k := by
    try dsimp [k]
    positivity [beta_pos hε]
  have hE : |E| ≤ q := by
    simpa [E, q] using! hphase
  have hP : |P - 1| ≤ k := by
    simpa [P, k] using!
      plusSaddleSmallRadiusPolynomial_error hε hℓ n hn
  have hexp : Real.exp E ≤ Real.exp q :=
    Real.exp_le_exp.mpr ((le_abs_self E).trans hE)
  have hexpabs : Real.exp |E| ≤ Real.exp q :=
    Real.exp_le_exp.mpr hE
  have htermP :
      |Real.exp E * (P - 1)| ≤ Real.exp q * k := by
    rw [abs_mul, abs_of_pos (Real.exp_pos E)]
    exact mul_le_mul hexp hP
      (abs_nonneg _) (Real.exp_pos q).le
  have htermE : |Real.exp E - 1| ≤ q * Real.exp q :=
    (abs_exp_sub_one_le_abs_mul_exp_abs E).trans
      (mul_le_mul hE hexpabs
        (Real.exp_pos |E|).le hq)
  change |Real.exp E * P - 1| ≤
    (q + k) * Real.exp q
  calc
    |Real.exp E * P - 1| =
        |Real.exp E * (P - 1) +
          (Real.exp E - 1)| := by
            congr 1
            ring
    _ ≤ |Real.exp E * (P - 1)| +
          |Real.exp E - 1| := abs_add_le _ _
    _ ≤ Real.exp q * k + q * Real.exp q :=
      add_le_add htermP htermE
    _ = (q + k) * Real.exp q := by ring
end CohnElkies
