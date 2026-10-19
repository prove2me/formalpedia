-- Prove2me | solution 1 for CohnElkies.radialProfile_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/2c8fd3d2-f119-4d6f-b3a9-defca21e2745

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_smooth
import Theorems.Thm_CohnElkies_radialProfile_deriv_zero

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ‖radialProfile hd f r‖ ≤ C * r ^ 2 := by
  have hsmooth :
      ContDiffOn ℝ (2 : ℕ∞)
        (radialProfile hd f) (Icc (0 : ℝ) 1) :=
    (radialProfile_smooth hd f 2).contDiffOn
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound
      (f := radialProfile hd f)
      (a := (0 : ℝ)) (b := (1 : ℝ)) (n := 1)
      zero_le_one hsmooth
  refine ⟨C, ?_⟩
  intro r hr hrone
  have hderivWithin :
      derivWithin (radialProfile hd f)
        (Icc (0 : ℝ) 1) 0 = 0 := by
    rw [DifferentiableAt.derivWithin
      ((radialProfile_smooth hd f 1).differentiable
        one_ne_zero 0)
      (uniqueDiffOn_Icc_zero_one 0 (by simp))]
    exact radialProfile_deriv_zero hd f hf
  have htaylor :
      taylorWithinEval (radialProfile hd f) 1
        (Icc (0 : ℝ) 1) 0 r = 0 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl,
      taylorWithinEval_succ]
    simp [radialProfile_zero, hzero,
      iteratedDerivWithin_one, hderivWithin]
  calc
    ‖radialProfile hd f r‖ =
        ‖radialProfile hd f r -
          taylorWithinEval (radialProfile hd f) 1
            (Icc (0 : ℝ) 1) 0 r‖ := by
      rw [htaylor, sub_zero]
    _ ≤ C * r ^ 2 := by
      simpa only [sub_zero, Nat.reduceAdd] using!
        hC r ⟨hr, hrone⟩
end CohnElkies
