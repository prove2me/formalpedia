-- Prove2me | solution 1 for CohnElkies.intervalIntegral_complexFrullaniLogDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/18d9785b-63bf-4370-a12b-bf0e2d4c42d5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniSegment_re_pos
import Theorems.Thm_CohnElkies_complexFrullaniSegment_hasDerivAt

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
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ s in (0 : ℝ)..1,
      (w - z) * (complexFrullaniSegment z w s)⁻¹) =
      Complex.log w - Complex.log z := by
  have hsegment :
      Continuous (fun s : ℝ => complexFrullaniSegment z w s) := by
    unfold complexFrullaniSegment
    fun_prop
  have hnonzero :
      ∀ s ∈ Set.uIcc (0 : ℝ) 1,
        complexFrullaniSegment z w s ≠ 0 := by
    intro s hs
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    exact ne_of_apply_ne Complex.re
      (complexFrullaniSegment_re_pos hz hw hs).ne'
  have hcontinuous :
      ContinuousOn
        (fun s : ℝ =>
          (w - z) * (complexFrullaniSegment z w s)⁻¹)
        (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (hsegment.continuousOn.inv₀ hnonzero)
  have hderiv (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt
        (fun r : ℝ => Complex.log (complexFrullaniSegment z w r))
        ((w - z) * (complexFrullaniSegment z w s)⁻¹) s := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hslit :
        complexFrullaniSegment z w s ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr
        (Or.inl (complexFrullaniSegment_re_pos hz hw hs))
    simpa [div_eq_mul_inv] using!
      (complexFrullaniSegment_hasDerivAt z w s).clog_real hslit
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcontinuous.intervalIntegrable]
  simp [complexFrullaniSegment]
end CohnElkies
