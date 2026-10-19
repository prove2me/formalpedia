-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_nonneg_of_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/51a99552-cc8a-47a7-b227-d2229023837f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialL1Mass_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hnonzero : g ≠ 0) {R : ℝ} (hR : 0 < R)
    (houtside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → 0 ≤ (g x).re)
    (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ normalizedRadialLogProfile hd g R v := by
  have hexp : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv
  have hradius : 0 < R * Real.exp v :=
    mul_pos hR (Real.exp_pos v)
  have hpoint :
      R ≤ ‖(R * Real.exp v) • radialUnitDirection hd‖ := by
    rw [norm_smul, norm_radialUnitDirection hd, mul_one,
      Real.norm_eq_abs, abs_of_pos hradius]
    calc
      R = R * 1 := (mul_one R).symm
      _ ≤ R * Real.exp v :=
        mul_le_mul_of_nonneg_left hexp hR.le
  unfold normalizedRadialLogProfile
  refine mul_nonneg (mul_nonneg ?_ (pow_nonneg hradius.le _)) ?_
  · exact (div_pos (radialSurfaceArea_pos hd)
      (radialL1Mass_pos g hnonzero)).le
  · exact houtside _ hpoint
end CohnElkies
