-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a44_true_stop_mask_positive_taylor_small_large_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:29:30.331683+00:00
-- url     : https://prove2.me/submissions/70424703-ef9c-45a1-812d-30c0e2e0dc1d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ga_a42_positive_taylor_small_large_energy_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open BigOperators AvramDividend.Classical
open scoped NNReal

-- Source-real stopped-cell positive C2 Taylor remainder bound with the true clock mask.
theorem solution {ι Ω : Type*} (S : Finset ι)
    (s : ι → ℝ≥0) (ρ : Ω → ℝ≥0) (ω : Ω)
    (a z : ι → Ω → ℝ) (ε M δ : ℝ)
    (hε : 0 ≤ ε)
    (ha : ∀ i ∈ S, s i < ρ ω → 0 ≤ a i ω)
    (hM : ∀ i ∈ S, s i < ρ ω → a i ω ≤ M)
    (hSmall : ∀ i ∈ S, s i < ρ ω →
      |z i ω| < δ → a i ω ≤ ε) :
    (∑ i ∈ S, if s i < ρ ω then a i ω * (z i ω)^2 else 0) ≤
      ε * (∑ i ∈ S, if s i < ρ ω then (z i ω)^2 else 0) +
      M * (∑ i ∈ S, if s i < ρ ω then
        (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0) := by
  classical
  change Finset.sum S (fun i => if s i < ρ ω then a i ω * (z i ω)^2 else 0) ≤
    ε * Finset.sum S (fun i => if s i < ρ ω then (z i ω)^2 else 0) +
    M * Finset.sum S (fun i => if s i < ρ ω then
      (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0)
  have hBound (i : ι) (hi : i ∈ S) :
      (if s i < ρ ω then a i ω * (z i ω)^2 else 0) ≤
      ε * (if s i < ρ ω then (z i ω)^2 else 0) +
      M * (if s i < ρ ω then
        (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0) := by
    by_cases h : s i < ρ ω
    · simp only [if_pos h]
      exact avram_ga_a42_positive_taylor_small_large_energy_split
        (a i ω) (z i ω) ε M δ
        (ha i hi h) hε (hM i hi h) (hSmall i hi h)
    · simp only [if_neg h, mul_zero, add_zero, le_refl]
  calc
    Finset.sum S (fun i => if s i < ρ ω then a i ω * (z i ω)^2 else 0) ≤
      Finset.sum S (fun i => ε * (if s i < ρ ω then (z i ω)^2 else 0) +
        M * (if s i < ρ ω then
          (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0)) :=
      Finset.sum_le_sum hBound
    _ = ε * Finset.sum S (fun i => if s i < ρ ω then (z i ω)^2 else 0) +
        M * Finset.sum S (fun i => if s i < ρ ω then
          (if δ ≤ |z i ω| then (z i ω)^2 else 0) else 0) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
