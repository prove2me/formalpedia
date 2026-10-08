-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_zero_of_ae_zero_restrict_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:30:41.784165+00:00
-- url     : https://prove2.me/submissions/7f902daf-f35b-4ff7-a86f-96936a9645e7

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ) [μ.IsOpenPosMeasure]
    (s : Set ℝ) (hs : IsOpen s)
    (f : ℝ → ℝ) (hf : ContinuousOn f s)
    (hae : ∀ᵐ x ∂(μ.restrict s), f x = 0) :
    ∀ x ∈ s, f x = 0 := by
  intro x hx
  have hcont : ContinuousAt f x := hf.continuousAt (hs.mem_nhds hx)
  have hxsupp : x ∈ (μ.restrict s).support := by
    apply Measure.interior_inter_support
    exact ⟨by simpa [hs.interior_eq] using hx, by simp [Measure.support_eq_univ]⟩
  by_contra hne
  have hnear : {z : ℝ | f z ≠ 0} ∈ 𝓝 x := by
    have hcod : {w : ℝ | w ≠ 0} ∈ 𝓝 (f x) :=
      isOpen_compl_singleton.mem_nhds hne
    exact hcont.eventually hcod
  have hpos : 0 < (μ.restrict s) {z : ℝ | f z ≠ 0} :=
    (Measure.mem_support_iff_forall x).1 hxsupp _ hnear
  have hzero : (μ.restrict s) {z : ℝ | f z ≠ 0} = 0 := by
    simpa only [ne_eq] using (ae_iff.mp hae)
  exact (lt_irrefl (0 : ℝ≥0∞)) (hpos.trans_eq hzero)
