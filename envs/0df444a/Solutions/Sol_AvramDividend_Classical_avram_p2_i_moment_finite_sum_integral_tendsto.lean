-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_finite_sum_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:28:55.044628+00:00
-- url     : https://prove2.me/submissions/07628637-a162-4e25-b0b7-218e2790f4b0

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped BigOperators

theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (s : Finset ℕ) (a : ℕ → ℝ)
    (hi : ∀ i k, k ∈ s → Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k ∈ s, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k ∈ s,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ))) :
    Tendsto (fun i => ∫ z : ℝ, (∑ k ∈ s, a k * z ^ k) ∂μi i) l
      (nhds (∫ z : ℝ, (∑ k ∈ s, a k * z ^ k) ∂μ)) := by
  classical
  have hlin (ν : Measure ℝ)
      (hν : ∀ k ∈ s, Integrable (fun z : ℝ => z ^ k) ν) :
      (∫ z : ℝ, (∑ k ∈ s, a k * z ^ k) ∂ν) =
        ∑ k ∈ s, a k * (∫ z : ℝ, z ^ k ∂ν) := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro k hk
      exact (hν k hk).const_mul _
  have hsum :
      Tendsto
        (fun i => ∑ k ∈ s, a k * (∫ z : ℝ, z ^ k ∂μi i))
        l (nhds (∑ k ∈ s, a k * (∫ z : ℝ, z ^ k ∂μ))) := by
    apply tendsto_finset_sum
    intro k hk
    exact tendsto_const_nhds.mul (hmom k hk)
  have heq :
      (fun i => ∫ z : ℝ, (∑ k ∈ s, a k * z ^ k) ∂μi i) =
      (fun i => ∑ k ∈ s, a k * (∫ z : ℝ, z ^ k ∂μi i)) := by
    funext i
    exact hlin (μi i) (hi i)
  rw [heq, hlin μ hμ]
  exact hsum
