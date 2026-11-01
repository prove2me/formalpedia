-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_pointwise_indicator_span_l2_lift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:39:02.882827+00:00
-- url     : https://prove2.me/submissions/2e8b6125-a851-4eaa-8b61-eb44a9f0013c

import Mathlib
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal NNReal

/-- A finite *pointwise* real combination of measurable finite-measure set
indicators becomes the same finite real combination in L²(μ). This is the
missing proof-irrelevant MemLp-to-Lp bridge needed after finite Boolean
Pi-system normalisation and before L² stochastic integral completion. -/
theorem solution
    {α : Type*} [mα : MeasurableSpace α]
    (μ : Measure α) (G : Set (Set α))
    (hGm : ∀ t : Set α, t ∈ G → MeasurableSet t)
    (hGfinite : ∀ t : Set α, t ∈ G → μ t ≠ ⊤)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hSpan :
      let χ : Set α → (α → ℝ) :=
        fun t => Set.indicator t (fun _ => (1 : ℝ))
      χ s ∈ Submodule.span ℝ
        {v : α → ℝ | ∃ (t : Set α), t ∈ G ∧ χ t = v}) :
    indicatorConstLp (2 : ℝ≥0∞) hs hμs (1 : ℝ) ∈
      Submodule.span ℝ
        {v : Lp ℝ (2 : ℝ≥0∞) μ |
          ∃ (t : Set α) (ht : t ∈ G)
            (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
            indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v} := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let χ : Set α → (α → ℝ) :=
    fun t => Set.indicator t (fun _ => (1 : ℝ))
  let S : Set (α → ℝ) :=
    {v | ∃ (t : Set α), t ∈ G ∧ χ t = v}
  let L : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
    {v | ∃ (t : Set α) (ht : t ∈ G)
      (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
      indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
  let M : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ) :=
    Submodule.span ℝ L
  change χ s ∈ Submodule.span ℝ S at hSpan
  change indicatorConstLp (2 : ℝ≥0∞) hs hμs (1 : ℝ) ∈ M
  have hLift (f : α → ℝ) (hf : f ∈ Submodule.span ℝ S) :
      ∃ (hfLp : MemLp f (2 : ℝ≥0∞) μ),
        hfLp.toLp f ∈ M := by
    induction hf using Submodule.span_induction with
    | mem u hu =>
      rcases hu with ⟨t, ht, rfl⟩
      have hmt : MemLp (χ t) (2 : ℝ≥0∞) μ :=
        memLp_indicator_const (2 : ℝ≥0∞) (hGm t ht)
          (1 : ℝ) (Or.inr (hGfinite t ht))
      refine ⟨hmt, ?_⟩
      exact Submodule.subset_span (R := ℝ) (s := L)
        ⟨t, ht, hGm t ht, hGfinite t ht, rfl⟩
    | zero =>
      refine ⟨MemLp.zero, ?_⟩
      simpa only [MemLp.toLp_zero] using M.zero_mem
    | add u v hu hv ihu ihv =>
      rcases ihu with ⟨huLp, huM⟩
      rcases ihv with ⟨hvLp, hvM⟩
      refine ⟨huLp.add hvLp, ?_⟩
      rw [MemLp.toLp_add huLp hvLp]
      exact M.add_mem huM hvM
    | smul c u hu ihu =>
      rcases ihu with ⟨huLp, huM⟩
      refine ⟨huLp.const_smul c, ?_⟩
      rw [MemLp.toLp_const_smul c huLp]
      exact M.smul_mem c huM
  rcases hLift (χ s) hSpan with ⟨hsLp, hsM⟩
  exact hsM

