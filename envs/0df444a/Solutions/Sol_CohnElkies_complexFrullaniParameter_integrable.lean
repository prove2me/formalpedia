-- Prove2me | solution 1 for CohnElkies.complexFrullaniParameter_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/0d64cdfa-b406-41f9-a929-cd8a16360c6d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexLaplaceKernel_integrable
import Theorems.Thm_CohnElkies_complexFrullaniSegment_re_pos
import Theorems.Thm_CohnElkies_integral_norm_complexFrullaniSegment

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
    Integrable
      (Function.uncurry (fun s x : ℝ =>
        (w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Ioi 0))) := by
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun s x : ℝ =>
          (w - z) *
            Complex.exp
              (-complexFrullaniSegment z w s * (x : ℂ))))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          (volume.restrict (Ioi 0))) := by
    unfold complexFrullaniSegment
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    exact
      (complexLaplaceKernel_integrable
        (complexFrullaniSegment_re_pos hz hw hclosed)).const_mul
          (w - z)
  · have hsegment :
        Continuous (fun s : ℝ =>
          (complexFrullaniSegment z w s).re) := by
        unfold complexFrullaniSegment
        fun_prop
    have hnonzero :
        ∀ s ∈ Set.uIcc (0 : ℝ) 1,
          (complexFrullaniSegment z w s).re ≠ 0 := by
      intro s hs
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      exact (complexFrullaniSegment_re_pos hz hw hs).ne'
    have hcontinuous :
        ContinuousOn
          (fun s : ℝ =>
            ‖w - z‖ *
              (complexFrullaniSegment z w s).re⁻¹)
          (Set.uIcc (0 : ℝ) 1) :=
      continuousOn_const.mul
        (hsegment.continuousOn.inv₀ hnonzero)
    have hintegrable :
        Integrable
          (fun s : ℝ =>
            ‖w - z‖ *
              (complexFrullaniSegment z w s).re⁻¹)
          (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
      intervalIntegrable_iff.mp
        (hcontinuous.intervalIntegrable)
    apply hintegrable.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc]
      with s hs
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    have hclosed : s ∈ Icc (0 : ℝ) 1 :=
      ⟨hs.1.le, hs.2⟩
    exact (integral_norm_complexFrullaniSegment hz hw hclosed).symm
end CohnElkies
