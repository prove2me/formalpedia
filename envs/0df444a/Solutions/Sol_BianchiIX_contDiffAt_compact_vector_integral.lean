-- Prove2me | solution 1 for BianchiIX.contDiffAt_compact_vector_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:08:18.494241+00:00
-- url     : https://prove2.me/submissions/30b15ba3-37d2-4b86-842f-82b4cdeed0bc

import Theorems.Thm_BianchiIX_hasFDerivAt_compact_vector_integral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


theorem solution {F : E × ℝ → V} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (x, t)) :
    ContDiffAt ℝ 1 (fun y => ∫ t in a..b, F (y, t)) x := by
  let D : E × ℝ → E →L[ℝ] V := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hDc {y : E} {t : ℝ} (h : ContDiffAt ℝ 1 F (y, t)) : ContinuousAt D (y, t) :=
    (h.continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const
  have hDt : ContinuousOn (fun t => D (x, t)) (Icc a b) := fun t ht =>
    ((hDc (hF t ht)).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hDt.norm
  let s : Set E := {y | ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (y, t) ∧ ‖D (y, t)‖ ≤ B + 1}
  have hs : s ∈ 𝓝 x := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hlt : ‖D (x, t)‖ < B + 1 := (hB (mem_image_of_mem _ ht)).trans_lt (lt_add_one B)
    exact ((hF t ht).eventually (by norm_num)).and
      (((hDc (hF t ht)).norm.eventually (isOpen_Iio.mem_nhds hlt)).mono fun _ h => h.le)
  apply contDiffAt_one_iff.mpr
  refine ⟨fun y => ∫ t in a..b, D (y, t), s, hs, ?_, ?_⟩
  · intro y hy
    apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => B + 1)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hcont : ContinuousOn (fun t => D (z, t)) (Icc a b) := fun t ht =>
        ((hDc (hz t ht).1).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      rw [uIoc_of_le hab]
      exact (hcont.intervalIntegrable_of_Icc hab).1.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact Eventually.of_forall fun t ht => (hz t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht)).2
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t ht =>
        ((hDc (hy t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht)).1).comp
          (f := fun z : E => (z, t)) (g := D)
          (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  · intro y hy
    exact hasFDerivAt_compact_vector_integral hab (fun t ht => (hy t ht).1)
