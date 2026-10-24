-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_full_kernel_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:01:15.78506+00:00
-- url     : https://prove2.me/submissions/b14a27d5-7018-4843-9606-80aac6f23b5b

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_continuousOn_positive
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_full_kernel_vanishes_origin
import Theorems.Thm_AvramDividend_Classical_causal_right_continuity_glue
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The weighted causal full-kernel integral extends continuously to time zero. -/
theorem solution
    (K : ℝ → ℝ) (β w : ℝ)
    (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
        (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)
      (Ici (0 : ℝ)) := by
  let V : ℝ → ℝ := fun s =>
    Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩
  let F : ℝ → ℝ := fun x =>
    ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume
  have hV : ContinuousOn V (Ici (0 : ℝ)) :=
    (causal_weighted_BCF_extension_continuous f w).continuousOn
  have hp : ContinuousOn F (Ioi (0 : ℝ)) :=
    causal_full_kernel_continuousOn_positive K V β hK hV
  have hzero : F 0 = 0 := by simp [F]
  have hlim : Tendsto F (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhds (F 0)) := by
    rw [hzero]
    exact causal_weighted_BCF_full_kernel_vanishes_origin K β w f hK
  exact causal_right_continuity_glue F hp hlim
