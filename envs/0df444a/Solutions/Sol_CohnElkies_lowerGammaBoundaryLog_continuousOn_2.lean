-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:25.610571+00:00
-- url     : https://prove2.me/submissions/e57b1f20-027a-4e0d-bed5-b90165543d7b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) {S : Set ℝ}
    (hS : ∀ y ∈ S, y ≠ 0) :
    ContinuousOn (lowerGammaBoundaryLog ℓ R) S := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  have h1 : ∀ m : ℕ, -Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.im h
    simp at this
    exact hS y hy (by linarith)
  have h2 : ∀ m : ℕ, (ℓ : ℂ) + Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := m.cast_nonneg
    linarith
  have hg1 : ContinuousAt (fun y : ℝ => Complex.Gamma (-Complex.I * (y : ℂ) / 2)) y :=
    ContinuousAt.comp (g := Complex.Gamma) (f := fun y : ℝ => -Complex.I * (y : ℂ) / 2)
      (Complex.differentiableAt_Gamma _ h1).continuousAt (by fun_prop)
  have hg2 : ContinuousAt (fun y : ℝ => Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)) y :=
    ContinuousAt.comp (g := Complex.Gamma) (f := fun y : ℝ => (ℓ : ℂ) + Complex.I * (y : ℂ) / 2)
      (Complex.differentiableAt_Gamma _ h2).continuousAt (by fun_prop)
  unfold lowerGammaBoundaryLog
  exact (continuousAt_const.add (hg1.norm.log (norm_ne_zero_iff.2 (Complex.Gamma_ne_zero h1)))).sub
    (hg2.norm.log (norm_ne_zero_iff.2 (Complex.Gamma_ne_zero h2)))

