-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:37:44.32262+00:00
-- url     : https://prove2.me/submissions/b79026db-a7a3-4476-96f7-836333316f10

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

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
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0)
    (H : ι → Ω → ℝ) (hH : ∀ i, StronglyMeasurable (H i))
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hBound : ∀ i ω, |H i ω| ≤ K i) :
    MemLp (fun ω => ∑ i ∈ S,
      H i ω * (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)) 2 P := by
  classical
  let Q : ι → Ω → ℝ := fun i ω =>
    H i ω * (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
      (h i : ℝ) * X.c)
  have hTerm (i : ι) : MemLp (Q i) 2 P := by
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (τ i) (hτ i) (T i) (hbounded i) (h i)
      (H i) (hH i) (K i) (hK i) (hBound i)
  change MemLp (fun ω => ∑ i ∈ S, Q i ω) 2 P
  exact memLp_finset_sum S (fun i hi => hTerm i)
