-- Prove2me | solution 1 for AvramDividend.Classical.nat_positive_martingale_finite_grid_maximal_unit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:51:05.437658+00:00
-- url     : https://prove2.me/submissions/175d09f3-accb-43ce-b20d-77d01f4c4eb4

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.ENNReal.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ mΩ}
    (Z : ℕ → Ω → ℝ) (hZ : Martingale Z 𝓕 μ)
    (hpos : ∀ n ω, 0 ≤ Z n ω)
    (hunit : ∀ n, (∫ ω, Z n ω ∂μ) = 1)
    (a : ℝ≥0) (n : ℕ) :
    (a : ℝ≥0∞) *
      μ {ω | (a : ℝ) ≤
        (Finset.range (n + 1)).sup'
          (Finset.nonempty_range_add_one) (fun k => Z k ω)} ≤ 1 := by
  have hnonneg : (0 : ℕ → Ω → ℝ) ≤ Z := by
    intro i ω
    exact hpos i ω
  have hm := maximal_ineq hZ.submartingale hnonneg (ε := a) n
  have hposAe : 0 ≤ᵐ[μ] Z n :=
    Filter.Eventually.of_forall (hpos n)
  have hle := setIntegral_le_integral (hZ.integrable n) hposAe
    (s := {ω | (a : ℝ) ≤
      (Finset.range (n + 1)).sup'
        (Finset.nonempty_range_add_one) (fun k => Z k ω)})
  calc
    (a : ℝ≥0∞) *
        μ {ω | (a : ℝ) ≤
          (Finset.range (n + 1)).sup'
            (Finset.nonempty_range_add_one) (fun k => Z k ω)} ≤
      ENNReal.ofReal
        (∫ ω in {ω | (a : ℝ) ≤
          (Finset.range (n + 1)).sup'
            (Finset.nonempty_range_add_one) (fun k => Z k ω)},
          Z n ω ∂μ) := hm
    _ ≤ ENNReal.ofReal (∫ ω, Z n ω ∂μ) :=
      ENNReal.ofReal_le_ofReal hle
    _ = 1 := by rw [hunit]; simp
