-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_iteratedDerivWithin_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/fa6e77b7-0ba4-40e4-92d6-6a60f6509e69

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_iteratedDeriv
import Theorems.Thm_CohnElkies_upperImaginaryExp_contDiff

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (n : ℕ) :
    iteratedDerivWithin n upperImaginaryExp (Icc a b) x =
      Complex.I ^ n * upperImaginaryExp x := by
  have hdiff :
      ContDiffAt ℝ (n : WithTop ℕ∞)
        upperImaginaryExp x :=
    upperImaginaryExp_contDiff.contDiffAt.of_le le_top
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc hab) hdiff hx,
    upperImaginaryExp_iteratedDeriv]
end CohnElkies
