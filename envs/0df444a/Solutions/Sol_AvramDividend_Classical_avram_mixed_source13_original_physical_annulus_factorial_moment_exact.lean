-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_original_physical_annulus_factorial_moment_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:40:18.010006+00:00
-- url     : https://prove2.me/submissions/cf94f5af-83d3-407a-ba05-521711313496

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
/-- Original annulus factorial mean from its physical finite-grid squeeze. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by
  classical
  have hsqueeze (r R z : ℝ)
      (h : ∀ k : ℕ,
        r ^ 2 * (1 - 1 / (((k + 1 : ℕ) : ℝ))) ≤ z ∧
        z ≤ r ^ 2 * (1 - 1 / (((k + 1 : ℕ) : ℝ))) +
          R ^ 2 / (((k + 1 : ℕ) : ℝ))) :
      z = r ^ 2 := by
    let δ : ℕ → ℝ := fun k => 1 / (((k + 1 : ℕ) : ℝ))
    have hδ : Tendsto δ atTop (nhds (0 : ℝ)) := by
      simpa only [δ, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hsub : Tendsto (fun k => (1 : ℝ) - δ k) atTop (nhds (1 : ℝ)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub hδ : Tendsto
          (fun k => (1 : ℝ) - δ k) atTop (nhds ((1 : ℝ) - 0)))
    have hlower : Tendsto (fun k => r ^ 2 * (1 - δ k)) atTop
        (nhds (r ^ 2)) := by
      simpa only [mul_one] using
        (tendsto_const_nhds.mul hsub : Tendsto
          (fun k => r ^ 2 * (1 - δ k)) atTop (nhds (r ^ 2 * 1)))
    have hextra : Tendsto (fun k => R ^ 2 * δ k) atTop (nhds (0 : ℝ)) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hδ : Tendsto
          (fun k => R ^ 2 * δ k) atTop (nhds (R ^ 2 * 0)))
    have hupper : Tendsto
        (fun k => r ^ 2 * (1 - δ k) + R ^ 2 * δ k)
        atTop (nhds (r ^ 2)) := by
      simpa only [add_zero] using hlower.add hextra
    have hlo : r ^ 2 ≤ z := by
      apply le_of_tendsto_of_tendsto hlower tendsto_const_nhds
      exact Filter.Eventually.of_forall (fun k => (h k).1)
    have hhi : z ≤ r ^ 2 := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hupper
      exact Filter.Eventually.of_forall (fun k => by
        simpa only [δ, mul_one_div] using (h k).2)
    exact le_antisymm hhi hlo
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  let R : ℝ := ((T : ℝ≥0∞) *
    X.ν (Iic (-(1 / ((m : ℝ) + 1))))).toReal
  change Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2
  obtain ⟨hInt, hGrid⟩ :=
    avram_mixed_source13_original_annulus_uniform_grid_factorial_sandwich
      X T n m hnm
  refine ⟨?_, ?_⟩
  · simpa only [N, B] using hInt
  · apply hsqueeze r R _
    intro k
    simpa only [N, B, r, R] using (hGrid k)
