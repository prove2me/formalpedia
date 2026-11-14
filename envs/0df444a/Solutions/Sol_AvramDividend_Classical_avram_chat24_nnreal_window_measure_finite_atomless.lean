-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_nnreal_window_measure_finite_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:57:52.527822+00:00
-- url     : https://prove2.me/submissions/cf1cdcf8-f3ae-45e9-a709-e60748060b0d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution (T : ℝ) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    IsFiniteMeasure μ ∧ ∀ t : ℝ≥0, μ {t} = 0 := by
  intro μ
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    change (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) Set.univ < ⊤
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  · intro t
    dsimp only [μ]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton t),
      Measure.restrict_apply
        ((measurableSet_singleton t).preimage (by fun_prop))]
    have hs : Real.toNNReal ⁻¹' ({t} : Set ℝ≥0) ∩ Icc 0 T ⊆ {(t : ℝ)} := by
      intro x hx
      have he : Real.toNNReal x = t := hx.1
      change x = (t : ℝ)
      simpa only [Real.coe_toNNReal x hx.2.1] using
        congrArg (fun z : ℝ≥0 => (z : ℝ)) he
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ (volume : Measure ℝ) {(t : ℝ)} := measure_mono hs
      _ = 0 := measure_singleton _
