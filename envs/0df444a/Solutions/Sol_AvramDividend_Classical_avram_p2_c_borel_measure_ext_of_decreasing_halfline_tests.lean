-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:15.07022+00:00
-- url     : https://prove2.me/submissions/183a9adf-e79f-4d8a-9a4f-dfc2f8e548de

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Agreement on shrinking half-line tests determines finite real Borel measures. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hApprox : ∀ a : ℝ, ∃ q : ℕ → ℝ,
      Antitone q ∧ Tendsto q atTop (𝓝 a) ∧
      (∀ n, a ≤ q n) ∧
      (∀ n, μ (Iic (q n)) = ν (Iic (q n)))) :
    μ = ν := by
  apply Measure.ext_of_Iic
  intro a
  obtain ⟨q, hAnti, hTendsto, hAbove, hTests⟩ := hApprox a
  have hSetAnti : Antitone (fun n : ℕ => Iic (q n)) := by
    intro i j hij x hx
    exact le_trans hx (hAnti hij)
  have hSetEq : (⋂ n : ℕ, Iic (q n)) = Iic a := by
    ext x
    simp only [mem_iInter, mem_Iic]
    constructor
    · intro hx
      by_contra hxa
      have hax : a < x := lt_of_not_ge hxa
      have hN : Iio x ∈ 𝓝 a := isOpen_Iio.mem_nhds hax
      obtain ⟨n, hn⟩ := (hTendsto.eventually hN).exists
      exact (not_lt_of_ge (hx n)) hn
    · intro hx n
      exact le_trans hx (hAbove n)
  have hFiniteμ : ∃ n : ℕ, μ (Iic (q n)) ≠ ⊤ := by
    refine ⟨0, ne_of_lt ?_⟩
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) IsFiniteMeasure.measure_univ_lt_top
  have hFiniteν : ∃ n : ℕ, ν (Iic (q n)) ≠ ⊤ := by
    refine ⟨0, ne_of_lt ?_⟩
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) IsFiniteMeasure.measure_univ_lt_top
  have hμInter :
      μ (⋂ n : ℕ, Iic (q n)) = ⨅ n : ℕ, μ (Iic (q n)) := by
    exact hSetAnti.measure_iInter (μ := μ)
      (fun n => measurableSet_Iic.nullMeasurableSet) hFiniteμ
  have hνInter :
      ν (⋂ n : ℕ, Iic (q n)) = ⨅ n : ℕ, ν (Iic (q n)) := by
    exact hSetAnti.measure_iInter (μ := ν)
      (fun n => measurableSet_Iic.nullMeasurableSet) hFiniteν
  calc
    μ (Iic a) = μ (⋂ n : ℕ, Iic (q n)) := by rw [hSetEq]
    _ = ⨅ n : ℕ, μ (Iic (q n)) := hμInter
    _ = ⨅ n : ℕ, ν (Iic (q n)) := by simp only [hTests]
    _ = ν (⋂ n : ℕ, Iic (q n)) := hνInter.symm
    _ = ν (Iic a) := by rw [hSetEq]
