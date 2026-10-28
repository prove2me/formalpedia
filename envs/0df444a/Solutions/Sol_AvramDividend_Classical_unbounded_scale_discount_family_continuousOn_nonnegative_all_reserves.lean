-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_nonnegative_all_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:52:15.28137+00:00
-- url     : https://prove2.me/submissions/ebf05b10-f145-439d-acdc-cbf545bece0f

import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn_all_reserves
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Continuity in nonnegative discount holds at every reserve, including zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ,
      ContinuousOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by
  intro x q hq
  let Q : ℝ := q + 1
  have hq0 : 0 ≤ q := hq
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hWQ : ∀ a ∈ Icc (0 : ℝ) Q, IsScaleFunction X a (W a) := by
    intro a ha
    exact hW a ha.1
  have hc := unbounded_scale_discount_family_continuousOn_all_reserves
    X hnbv Q hQ W hWQ x
  have hqIcc : q ∈ Icc (0 : ℝ) Q := by
    constructor
    · exact hq
    · dsimp [Q]
      linarith
  have hqQ : q < Q := by dsimp [Q]; linarith
  have heq : Icc (0 : ℝ) Q =ᶠ[𝓝 q] Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hqQ] with y hy
    apply propext
    constructor
    · intro hycc
      exact hycc.1
    · intro hyci
      exact ⟨hyci, le_of_lt hy⟩
  exact (hc q hqIcc).congr_set heq
