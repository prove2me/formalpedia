-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_tsum_effective_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:23:57.646499+00:00
-- url     : https://prove2.me/submissions/90565e35-9cef-44fc-92af-6845abde33dc

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Removing zero source singleton Cash atoms preserves the literal real discounted sum. -/
theorem solution
    (A : Set ℝ) (μatom : Measure ℝ) (q : ℝ) :
    (∑' a : A,
      (ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}).toReal) =
    ∑' a : {a : A // μatom {a.1} ≠ 0},
      (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
        μatom {a.1.1}).toReal := by
  let f : A → ℝ := fun a =>
    (ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}).toReal
  let B : Set A := {a | μatom {a.1} ≠ 0}
  have hsupport : Function.support f ⊆ B := by
    intro a ha
    by_contra hnot
    have hzero : μatom {a.1} = 0 := by
      simpa [B] using hnot
    have hfzero : f a = 0 := by simp [f, hzero]
    exact ha hfzero
  change (∑' a : A, f a) = ∑' a : B, f a.1
  exact (tsum_subtype_eq_of_support_subset hsupport).symm
