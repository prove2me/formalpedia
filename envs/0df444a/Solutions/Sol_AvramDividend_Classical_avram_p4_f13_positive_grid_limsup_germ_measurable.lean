-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f13_positive_grid_limsup_germ_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:27:14.750522+00:00
-- url     : https://prove2.me/submissions/1f11b84d-16e1-421b-873c-b24c41aaa21d

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_DurrettProbability_Brownian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false

open MeasureTheory Filter Set DurrettProbability
open scoped NNReal Topology

/-- Positive observations infinitely often on a shrinking grid are a germ event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (δ : ℕ → ℝ≥0)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    MeasurableSet[germSigma B]
      (⋂ k : ℕ, ⋃ n : ℕ,
        {ω : Ω | k ≤ n ∧ 0 < B (δ n) ω}) := by
  let A (k n : ℕ) : Set Ω := {ω : Ω | k ≤ n ∧ 0 < B (δ n) ω}
  have hshift (N : ℕ) :
      (⋂ k : ℕ, ⋃ n : ℕ, A k n) =
        (⋂ k : ℕ, ⋃ n : ℕ, A (max N k) n) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_iUnion, A, Set.mem_setOf_eq]
    constructor
    · intro h k
      obtain ⟨n, hn, hv⟩ := h (max N k)
      exact ⟨n, hn, hv⟩
    · intro h k
      obtain ⟨n, hn, hv⟩ := h k
      exact ⟨n, le_trans (le_max_right N k) hn, hv⟩
  have hS (s : ℝ≥0) (hs : 0 < s) :
      MeasurableSet[pastSigma B s]
        (⋂ k : ℕ, ⋃ n : ℕ, A k n) := by
    have he : ∀ᶠ n : ℕ in atTop, δ n < s :=
      hδ.eventually (Iio_mem_nhds hs)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
    rw [hshift N]
    refine MeasurableSet.iInter (fun k => ?_)
    refine MeasurableSet.iUnion (fun n => ?_)
    by_cases hn : max N k ≤ n
    · have htn : δ n ≤ s :=
        (hN n (le_trans (le_max_left N k) hn)).le
      have hcoord : Measurable[pastSigma B s] (B (δ n)) := by
        apply measurable_iff_comap_le.mpr
        unfold pastSigma
        exact le_iSup_of_le (δ n) (le_iSup_of_le htn le_rfl)
      change MeasurableSet[pastSigma B s]
        {ω : Ω | max N k ≤ n ∧ 0 < B (δ n) ω}
      simpa only [hn, true_and] using
        (measurableSet_lt
          (measurable_const : Measurable[pastSigma B s] (fun _ : Ω => (0 : ℝ)))
          hcoord)
    · change MeasurableSet[pastSigma B s]
        {ω : Ω | max N k ≤ n ∧ 0 < B (δ n) ω}
      simp [hn]
  unfold germSigma
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro s
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro hs
  simpa only [A] using hS s hs
