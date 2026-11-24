-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.intervalIntegrable_sum_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:28.745057+00:00
-- url     : https://prove2.me/submissions/c9c910c4-07aa-455a-9cb3-5eb3b4fd121f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (c : ℕ → ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  have hmeas : Measurable (fun t : ℝ => ∑ n ∈ Icc 0 ⌊t⌋₊, c n) :=
    (measurable_from_nat (f := fun m => ∑ n ∈ Icc 0 m, c n)).comp Nat.measurable_floor
  set B : ℝ := ∑ n ∈ Icc 0 ⌊b⌋₊, |c n| with hB
  have hbound : IntervalIntegrable (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) MeasureTheory.volume a b := by
    refine IntervalIntegrable.mono_fun' (f := fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n)) (g := fun _ => B)
      intervalIntegrable_const hmeas.aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have htb : t ≤ b := by
      have := ht.2
      simpa [max_eq_right hab] using this
    show ‖∑ n ∈ Icc 0 ⌊t⌋₊, c n‖ ≤ B
    rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono htb)) (fun _ _ _ => abs_nonneg _)
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.uIcc a b) := by
    have hpos : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans (le_trans ha (le_min le_rfl hab)) ht.1
    apply ContinuousOn.div continuousOn_const
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.pow
      exact Real.continuousOn_log.mono (fun t ht => by simp; linarith [hpos t ht])
    · intro t ht
      have h2 := hpos t ht
      exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
  have he : (fun t : ℝ => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2)) =
      fun t => (∑ n ∈ Icc 0 ⌊t⌋₊, c n) * (1 / (t * Real.log t ^ 2)) := by
    funext t
    ring
  rw [he]
  exact hbound.mul_continuousOn hc
end Formalism.HermitianLattices.Ext.PrimesInProgressions
