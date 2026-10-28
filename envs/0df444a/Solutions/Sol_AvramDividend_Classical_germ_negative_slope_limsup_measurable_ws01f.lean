-- Prove2me | solution 1 for AvramDividend.Classical.germ_negative_slope_limsup_measurable_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:18:01.99127+00:00
-- url     : https://prove2.me/submissions/d04c8691-c41b-4a5a-a991-a5d0de143110

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_DurrettProbability_Brownian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter Set DurrettProbability
open scoped NNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (δ : ℕ → ℝ≥0)
    (hδ : Tendsto δ atTop (𝓝 0)) (C : ℝ) :
    MeasurableSet[germSigma B]
      (⋂ k : ℕ, ⋃ n : ℕ,
        {ω : Ω | k ≤ n ∧ B (δ n) ω < C * (δ n : ℝ)}) := by
  let A (k n : ℕ) : Set Ω :=
    {ω : Ω | k ≤ n ∧ B (δ n) ω < C * (δ n : ℝ)}
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
        {ω : Ω | max N k ≤ n ∧ B (δ n) ω < C * (δ n : ℝ)}
      simpa only [hn, true_and] using
        (measurableSet_lt hcoord
          (measurable_const : Measurable[pastSigma B s]
            (fun _ : Ω => C * (δ n : ℝ))))
    · change MeasurableSet[pastSigma B s]
        {ω : Ω | max N k ≤ n ∧ B (δ n) ω < C * (δ n : ℝ)}
      simp [hn]
  unfold germSigma
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro s
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro hs
  simpa only [A] using hS s hs
