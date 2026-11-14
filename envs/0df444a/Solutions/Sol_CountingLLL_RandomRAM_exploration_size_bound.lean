-- Prove2me | solution 1 for CountingLLL.RandomRAM.exploration_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:07:34.765849+00:00
-- url     : https://prove2.me/submissions/6a59592f-e297-40b0-8ce5-3e550d600bb7

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

/-- Expected accepted-tree size from a bounded number of adaptive tests.
`tested j` records whether test j occurs; `accepted j` records its success. The per-test
probability assumption may be obtained by conditioning on the previous exploration transcript. -/
theorem solution {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (root : Set Ω) (tested accepted : ι → Set Ω) (p p0 D : ℝ)
    (hroot : MeasurableSet root) (htested : ∀ j, MeasurableSet (tested j))
    (haccepted : ∀ j, MeasurableSet (accepted j))
    (hp : 0 ≤ p) (hsub : p * D^2 < 1)
    (hrootprob : μ.real root ≤ p0)
    (hlocal : ∀ j, μ.real (accepted j) ≤ p * μ.real (tested j))
    (hsteps : ∀ ω,
      (∑ j, (tested j).indicator (1 : Ω → ℝ) ω) ≤ D^2 *
      (root.indicator (1 : Ω → ℝ) ω + ∑ j, (accepted j).indicator (1 : Ω → ℝ) ω)) :
    (∫ ω, root.indicator (1 : Ω → ℝ) ω +
      ∑ j, (accepted j).indicator (1 : Ω → ℝ) ω ∂μ) ≤ p0 / (1-p*D^2) := by
  let R : Ω → ℝ := root.indicator 1
  let A : ι → Ω → ℝ := fun j => (tested j).indicator 1
  let B : ι → Ω → ℝ := fun j => (accepted j).indicator 1
  let T : Ω → ℝ := fun ω => R ω + ∑ j, B j ω
  let N : Ω → ℝ := fun ω => ∑ j, A j ω
  have hRint : Integrable R μ := by
    exact (integrable_const (1 : ℝ)).indicator hroot
  have hAint : ∀ j, Integrable (A j) μ := fun j => (integrable_const (1 : ℝ)).indicator (htested j)
  have hBint : ∀ j, Integrable (B j) μ := fun j => (integrable_const (1 : ℝ)).indicator (haccepted j)
  have hNint : Integrable N μ := integrable_finsetSum Finset.univ (fun j _ => hAint j)
  have hTint : Integrable T μ := hRint.add (integrable_finsetSum Finset.univ (fun j _ => hBint j))
  have hRmean : (∫ ω, R ω ∂μ) = μ.real root := integral_indicator_one hroot
  have hAmean : ∀ j, (∫ ω, A j ω ∂μ) = μ.real (tested j) := fun j => integral_indicator_one (htested j)
  have hBmean : ∀ j, (∫ ω, B j ω ∂μ) = μ.real (accepted j) := fun j => integral_indicator_one (haccepted j)
  have hNmean : (∫ ω, N ω ∂μ) = ∑ j, μ.real (tested j) := by
    dsimp [N]
    rw [integral_finsetSum Finset.univ (fun j _ => hAint j)]
    simp_rw [hAmean]
  have hTmean : (∫ ω, T ω ∂μ) = μ.real root + ∑ j, μ.real (accepted j) := by
    dsimp [T]
    rw [integral_add hRint (integrable_finsetSum Finset.univ (fun j _ => hBint j)), hRmean,
      integral_finsetSum Finset.univ (fun j _ => hBint j)]
    simp_rw [hBmean]
  have hNbound : (∫ ω, N ω ∂μ) ≤ D^2 * (∫ ω, T ω ∂μ) := by
    have h := integral_mono hNint (hTint.const_mul (D^2)) hsteps
    simpa only [integral_const_mul] using h
  have hBbound : (∑ j, μ.real (accepted j)) ≤ p * (∑ j, μ.real (tested j)) := by
    calc
      _ ≤ ∑ j, p * μ.real (tested j) := Finset.sum_le_sum (fun j _ => hlocal j)
      _ = _ := by rw [Finset.mul_sum]
  have hest : (∫ ω, T ω ∂μ) ≤ p0 + p * D^2 * (∫ ω, T ω ∂μ) := by
    have hh := mul_le_mul_of_nonneg_left hNbound hp
    rw [hNmean] at hh
    rw [hTmean]
    nlinarith
  have hden : 0 < 1-p*D^2 := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith
