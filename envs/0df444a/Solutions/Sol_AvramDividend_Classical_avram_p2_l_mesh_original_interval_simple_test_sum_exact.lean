-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_original_interval_simple_test_sum_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:16:34.103317+00:00
-- url     : https://prove2.me/submissions/6dd803b7-e464-48f9-93e0-ed94756634e9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_weighted_indicator_finset_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- Every finite interval-step test of the original uniform-grid marks
eventually sums to the intrinsic-jump test, uniformly over real weights. -/
theorem solution {ι : Type*} [Fintype ι]
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (a b : ι → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hbneg : ∀ i, b i ≤ -ρ)
    (hEndpoint : ∀ (i : ι) (u : ℝ≥0), 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a i ∧
        Y u - Function.leftLim Y u ≠ b i)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ c : ι → ℝ,
        (∑ j ∈ Finset.range (n + 1), ∑ i : ι,
          if Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
              Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈
                Ioc (a i) (b i) then c i else 0) =
        (∑ u ∈ S, ∑ i : ι,
          if Y u - Function.leftLim Y u ∈ Ioc (a i) (b i)
          then c i else 0) := by
  classical
  obtain ⟨S, hS, hCounts⟩ :=
    avram_p2_l_mesh_finite_negative_intervals_counts_eventually_exact
      Y T hT a b ρ hρ hbneg hEndpoint hL hR
  refine ⟨S, hS, ?_⟩
  filter_upwards [hCounts] with n hn c
  let g : ℕ → ℝ := fun j =>
    Y (((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
      Y ((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
  let δ : ℝ≥0 → ℝ := fun u => Y u - Function.leftLim Y u
  have hcount (i : ι) :
      ((Finset.range (n + 1)).filter
        (fun j => g j ∈ Ioc (a i) (b i))).card =
        (S.filter (fun u => δ u ∈ Ioc (a i) (b i))).card := by
    simpa only [g, δ] using hn i
  change (∑ j ∈ Finset.range (n + 1), ∑ i : ι,
      if g j ∈ Ioc (a i) (b i) then c i else 0) =
    (∑ u ∈ S, ∑ i : ι,
      if δ u ∈ Ioc (a i) (b i) then c i else 0)
  calc
    _ = ∑ i : ι, ∑ j ∈ Finset.range (n + 1),
          if g j ∈ Ioc (a i) (b i) then c i else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : ι,
          (((Finset.range (n + 1)).filter
            (fun j => g j ∈ Ioc (a i) (b i))).card : ℝ) * c i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              _ = ∑ j ∈ (Finset.range (n + 1)).filter
                    (fun j => g j ∈ Ioc (a i) (b i)), c i := by
                      rw [Finset.sum_filter]
              _ = _ := by simp
    _ = ∑ i : ι,
          ((S.filter (fun u => δ u ∈ Ioc (a i) (b i))).card : ℝ) * c i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcount i]
    _ = ∑ i : ι, ∑ u ∈ S,
          if δ u ∈ Ioc (a i) (b i) then c i else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            symm
            calc
              _ = ∑ u ∈ S.filter
                    (fun u => δ u ∈ Ioc (a i) (b i)), c i := by
                      rw [Finset.sum_filter]
              _ = _ := by simp
    _ = _ := by rw [Finset.sum_comm]
