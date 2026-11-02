-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_sigma_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:13:43.950751+00:00
-- url     : https://prove2.me/submissions/1f27349e-31c1-40d2-91e6-4defdcd3a4e1

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_sigma_bound

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
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let Q : ι → Ω → ℝ := fun i ω =>
      ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
        max (-K) (min K (G (s i) ω))) *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)
    (∫ ω, (∑ i ∈ S, Q i ω) ^ 2 ∂P) ≤
      (S.card : ℝ) *
        (∑ i ∈ S, (‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K) ^ 2 *
          ((h i : ℝ) * X.σ ^ 2)) := by
  classical
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    let y := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
  let Q : ι → Ω → ℝ := fun i ω =>
    ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
      max (-K) (min K (G (s i) ω))) *
    (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c)
  change (∫ ω, (∑ i ∈ S, Q i ω) ^ 2 ∂P) ≤
    (S.card : ℝ) *
      (∑ i ∈ S, (‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K) ^ 2 *
        ((h i : ℝ) * X.σ ^ 2))
  have hMem : MemLp (fun ω => ∑ i ∈ S, Q i ω) 2 P := by
    have ht :=
      avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
        X hν x D hD w C hw S s q K hK τ hτ T hbounded h
    change MemLp (fun ω => ∑ i ∈ S, Q i ω) 2 P at ht
    exact ht
  have hCellMem (i : ι) : MemLp (Q i) 2 P := by
    have ht :=
      avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
        X hν x D hD w C hw (s i) q K hK
        (τ i) (hτ i) (T i) (hbounded i) (h i)
    change MemLp (Q i) 2 P at ht
    exact ht
  have hInt1 :
      Integrable (fun ω => (∑ i ∈ S, Q i ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMem.aestronglyMeasurable).mp hMem
  have hInt2 :
      Integrable (fun ω => ∑ i ∈ S, (Q i ω) ^ 2) P := by
    apply integrable_finset_sum S
    intro i hi
    exact (memLp_two_iff_integrable_sq
      (hCellMem i).aestronglyMeasurable).mp (hCellMem i)
  have hCS :
      (∫ ω, (∑ i ∈ S, Q i ω) ^ 2 ∂P) ≤
        (S.card : ℝ) * (∫ ω, ∑ i ∈ S, (Q i ω) ^ 2 ∂P) := by
    calc
      (∫ ω, (∑ i ∈ S, Q i ω) ^ 2 ∂P) ≤
          (∫ ω, (S.card : ℝ) * ∑ i ∈ S, (Q i ω) ^ 2 ∂P) := by
        apply integral_mono hInt1 (hInt2.const_mul _)
        intro ω
        exact sq_sum_le_card_mul_sum_sq
      _ = (S.card : ℝ) * (∫ ω, ∑ i ∈ S, (Q i ω) ^ 2 ∂P) := by
        rw [integral_const_mul]
  have hEnergy :
      (∫ ω, ∑ i ∈ S, (Q i ω) ^ 2 ∂P) ≤
        ∑ i ∈ S, (‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K) ^ 2 *
          ((h i : ℝ) * X.σ ^ 2) := by
    have ht :=
      avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_sigma_bound
        X hν x D hD w C hw S s q K hK τ hτ T hbounded h
    change (∫ ω, ∑ i ∈ S, (Q i ω) ^ 2 ∂P) ≤
      ∑ i ∈ S, (‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K) ^ 2 *
        ((h i : ℝ) * X.σ ^ 2) at ht
    exact ht
  exact hCS.trans (mul_le_mul_of_nonneg_left hEnergy (Nat.cast_nonneg _))