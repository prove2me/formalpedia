-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_source_count_coupling_implies_singleton_law_limit_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:15:51.436176+00:00
-- url     : https://prove2.me/submissions/6f84f52b-93fb-48de-bf8e-784797138a01

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (Z : ℕ → Ω → ℕ) (hZ : ∀ n, Measurable (Z n))
    (p : ℕ → unitInterval)
    (hLaw : ∀ n, P.map (Z n) = Bin(n, p n))
    (hBad : Tendsto (fun n : ℕ =>
      (P {ω : Ω | K ω ≠ Z n ω}).toReal)
      atTop (𝓝 (0 : ℝ))) :
    ∀ k : ℕ,
      Tendsto (fun n : ℕ => (Bin(n, p n) {k}).toReal)
        atTop (𝓝 ((P.map K) {k}).toReal) := by
  intro k
  let a : ℝ := (P.map K {k}).toReal
  let b : ℕ → ℝ := fun n => (Bin(n, p n) {k}).toReal
  let e : ℕ → ℝ := fun n => (P {ω : Ω | K ω ≠ Z n ω}).toReal
  have hKfinite : P.map K {k} ≠ ⊤ := by
    rw [Measure.map_apply hK (measurableSet_singleton k)]
    exact measure_ne_top P _
  have hEfinite (n : ℕ) : P {ω : Ω | K ω ≠ Z n ω} ≠ ⊤ :=
    measure_ne_top P _
  have hBfinite (n : ℕ) : Bin(n, p n) {k} ≠ ⊤ :=
    measure_ne_top _ _
  have hu (n : ℕ) : b n ≤ a + e n := by
    have h := (avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
      P K (Z n) hK (hZ n) k).2
    rw [hLaw n] at h
    have hb : Bin(n, p n) {k} ≤
        P.map K {k} + P {ω : Ω | K ω ≠ Z n ω} := h
    have hfin : P.map K {k} +
        P {ω : Ω | K ω ≠ Z n ω} ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨hKfinite, hEfinite n⟩
    have hto := ENNReal.toReal_mono hfin hb
    simpa only [a, b, e, ENNReal.toReal_add hKfinite (hEfinite n)] using hto
  have hl (n : ℕ) : a - e n ≤ b n := by
    have h := (avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
      P K (Z n) hK (hZ n) k).1
    rw [hLaw n] at h
    have hfin : Bin(n, p n) {k} +
        P {ω : Ω | K ω ≠ Z n ω} ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨hBfinite n, hEfinite n⟩
    have hto := ENNReal.toReal_mono hfin h
    have hre : a ≤ b n + e n := by
      simpa only [a, b, e, ENNReal.toReal_add (hBfinite n) (hEfinite n)] using hto
    linarith
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) := hBad
  have htleft : Tendsto (fun n : ℕ => a - e n) atTop (𝓝 a) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub he)
  have htright : Tendsto (fun n : ℕ => a + e n) atTop (𝓝 a) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).add he)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' htleft htright
    (Filter.Eventually.of_forall hl) (Filter.Eventually.of_forall hu)
