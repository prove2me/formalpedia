-- Prove2me | solution 1 for BianchiIX.hasFDerivAt_compact_vector_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:06:25.736196+00:00
-- url     : https://prove2.me/submissions/8fffac58-d4b9-42ff-96dc-a19e52e258bb

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


/-- The vector-valued version also applies to the operator-valued first derivative. -/
theorem solution {F : E × ℝ → V} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (x, t)) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y, t))
      (∫ t in a..b, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] V := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hDc (t : ℝ) (ht : t ∈ Icc a b) : ContinuousAt D (x, t) :=
    ((hF t ht).continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const
  have hDt : ContinuousOn (fun t => D (x, t)) (Icc a b) := fun t ht =>
    ((hDc t ht).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hDt.norm
  let s : Set E := {y | ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (y, t) ∧ ‖D (y, t)‖ ≤ B + 1}
  have hs : s ∈ 𝓝 x := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hlt : ‖D (x, t)‖ < B + 1 := (hB (mem_image_of_mem _ ht)).trans_lt (lt_add_one B)
    exact ((hF t ht).eventually (by norm_num)).and
      (((hDc t ht).norm.eventually (isOpen_Iio.mem_nhds hlt)).mono fun _ h => h.le)
  have hc (y : E) (hy : y ∈ s) : ContinuousOn (fun t => F (y, t)) (Icc a b) :=
    fun t ht => (((hy t ht).1.continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hD (y : E) (hy : y ∈ s) (t : ℝ) (ht : t ∈ Icc a b) :
      HasFDerivAt (fun z => F (z, t)) (D (y, t)) y := by
    have hp : HasFDerivAt (fun z : E => (z, t)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
      convert! (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const t y) using 1
    exact ((hy t ht).1.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (f := fun z : E => (z, t)) (g := F) hp
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => F (y, t)) (F' := fun y t => D (y, t)) (bound := fun _ => B + 1) hs
  · filter_upwards [hs] with y hy
    rw [uIoc_of_le hab]
    exact ((hc y hy).intervalIntegrable_of_Icc hab).1.aestronglyMeasurable
  · exact (hc x (mem_of_mem_nhds hs)).intervalIntegrable_of_Icc hab
  · rw [uIoc_of_le hab]
    exact (hDt.intervalIntegrable_of_Icc hab).1.aestronglyMeasurable
  · exact Eventually.of_forall fun t ht y hy =>
      (hy t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht)).2
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht y hy => hD y hy t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht)
