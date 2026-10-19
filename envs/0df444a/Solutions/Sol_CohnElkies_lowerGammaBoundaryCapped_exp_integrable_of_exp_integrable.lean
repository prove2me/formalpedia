-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/e42a0e57-62ff-4f1f-9cdb-c7667a5dbb3d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_strip_exp_abs_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (R D : ℝ)
    (hgamma : Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) * lowerGammaBoundaryLog ℓ R y)) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryCapped ℓ R D y) := by
  have hgammaabs : Integrable
      (fun y : ℝ =>
        Real.exp ((-a) * |y|) *
          |lowerGammaBoundaryLog ℓ R y|) := by
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)] using! hgamma.norm
  have hbase := strip_exp_abs_integrable ha
  have hmajor : Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
          |lowerGammaBoundaryLog ℓ R y| +
        |D| * Real.exp ((-a) * |y|)) :=
    hgammaabs.add (hbase.const_mul |D|)
  have hweight : Continuous
      (fun y : ℝ => Real.exp ((-a) * |y|)) := by
    fun_prop
  apply hmajor.mono'
    ((hweight.mul
      (lowerGammaBoundaryCapped_continuous
        hℓ R D)).aestronglyMeasurable)
  filter_upwards [Measure.ae_ne
    (volume : Measure ℝ) 0] with y hy
  have hcap :
      |lowerGammaBoundaryCapped ℓ R D y| ≤
        |lowerGammaBoundaryLog ℓ R y| + |D| := by
    unfold lowerGammaBoundaryCapped
    rw [if_neg hy]
    rcases le_total (lowerGammaBoundaryLog ℓ R y) D
      with hleft | hright
    · rw [min_eq_left hleft]
      exact le_add_of_nonneg_right (abs_nonneg D)
    · rw [min_eq_right hright]
      exact le_add_of_nonneg_left
        (abs_nonneg (lowerGammaBoundaryLog ℓ R y))
  change
    |Real.exp ((-a) * |y|) *
      lowerGammaBoundaryCapped ℓ R D y| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp ((-a) * |y|) *
        |lowerGammaBoundaryCapped ℓ R D y| ≤
      Real.exp ((-a) * |y|) *
        (|lowerGammaBoundaryLog ℓ R y| + |D|) :=
      mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
    _ = Real.exp ((-a) * |y|) *
          |lowerGammaBoundaryLog ℓ R y| +
        |D| * Real.exp ((-a) * |y|) := by
      ring
end CohnElkies
