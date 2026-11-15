-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a411_unique_masked_uniform_vanishing_abs_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:27:59.070648+00:00
-- url     : https://prove2.me/submissions/aa97d314-9f82-47ce-bacd-d926c0f0e8aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a394_unique_masked_sum_absolute_dominated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (Mask : ℕ → ℕ → Prop) [∀ m i, Decidable (Mask m i)]
    (F : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (hUnique : ∀ m i j, Mask m i → Mask m j → i = j)
    (hRaw : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ i < m, |F m i| < ε / 2)
    (hDrift : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |d m| ≤ ε / 2) :
    Tendsto (fun m : ℕ =>
      ∑ i ∈ Finset.range m, if Mask m i then |F m i - d m| else 0)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  apply Metric.tendsto_atTop.2
  intro ε hε
  have he : 0 < ε / 2 := by linarith
  have hevent := (hRaw (ε / 2) he).and (hDrift (ε / 2) he)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨k, ?_⟩
  intro m hm
  obtain ⟨hr, hd⟩ := hk m hm
  let S : ℝ := ∑ i ∈ Finset.range m,
    if Mask m i then |F m i - d m| else 0
  have hsum : |S| ≤ ε / 2 := by
    apply avram_ga_a394_unique_masked_sum_absolute_dominated
      m (Mask m) (fun i => |F m i - d m|)
      (ε / 2) (le_of_lt he) (hUnique m)
    intro i hi hmask
    rw [abs_abs]
    calc
      |F m i - d m| ≤ |F m i| + |d m| := abs_sub _ _
      _ ≤ ε / 2 := by linarith [hr i hi]
  have hs : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hbound : S ≤ ε / 2 := by simpa [abs_of_nonneg hs] using hsum
  have hsmall : S < ε := lt_of_le_of_lt hbound (by linarith)
  change dist S 0 < ε
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hs] using hsmall
