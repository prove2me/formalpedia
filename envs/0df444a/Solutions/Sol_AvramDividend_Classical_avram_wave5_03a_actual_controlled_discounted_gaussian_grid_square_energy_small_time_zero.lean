-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_small_time_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:47:22.768221+00:00
-- url     : https://prove2.me/submissions/6cea6e75-c2b2-4c53-a9d1-1a13f9375c88

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_L2_small_time_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ι) (s : ι → ℝ≥0) (q K : ℝ) (hK : 0 ≤ K)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    Filter.Tendsto (fun h : ℝ≥0 =>
      (∫ ω, ∑ i ∈ S,
        (((Real.exp (-(q * (s i : ℝ))) * X.σ) *
            max (-K) (min K (G (s i) ω))) *
          (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
            (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  classical
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    let y := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
  let Q : ι → ℝ≥0 → Ω → ℝ := fun i h ω =>
    ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
      max (-K) (min K (G (s i) ω))) *
    (X.X (τ i ω + h) ω - X.X (τ i ω) ω - (h : ℝ) * X.c)
  change Filter.Tendsto
    (fun h : ℝ≥0 => ∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P)
    (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ))
  have hMem (i : ι) (h : ℝ≥0) : MemLp (Q i h) 2 P := by
    have ht :=
      avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
        X hν x D hD w C hw (s i) q K hK
        (τ i) (hτ i) (T i) (hbounded i) h
    change MemLp (Q i h) 2 P at ht
    exact ht
  have hInt (i : ι) (h : ℝ≥0) :
      Integrable (fun ω => (Q i h ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq (hMem i h).aestronglyMeasurable).mp (hMem i h)
  have hCell (i : ι) :
      Filter.Tendsto (fun h : ℝ≥0 => ∫ ω, (Q i h ω) ^ 2 ∂P)
        (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    have ht :=
      avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_L2_small_time_zero
        X hν x D hD w C hw (s i) q K hK
        (τ i) (hτ i) (T i) (hbounded i)
    change Filter.Tendsto
      (fun h : ℝ≥0 => ∫ ω, (Q i h ω) ^ 2 ∂P)
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) at ht
    exact ht
  have hId (h : ℝ≥0) :
      (∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P) =
        ∑ i ∈ S, ∫ ω, (Q i h ω) ^ 2 ∂P := by
    exact integral_finset_sum S (fun i hi => hInt i h)
  have hSum : Filter.Tendsto
      (fun h : ℝ≥0 => ∑ i ∈ S, ∫ ω, (Q i h ω) ^ 2 ∂P)
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    have ht := tendsto_finset_sum S (fun i hi => hCell i)
    simpa only [Finset.sum_const_zero] using ht
  apply hSum.congr'
  filter_upwards [] with h
  exact (hId h).symm
