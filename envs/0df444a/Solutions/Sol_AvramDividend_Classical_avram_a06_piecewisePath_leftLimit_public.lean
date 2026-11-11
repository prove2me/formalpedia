-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_piecewisePath_leftLimit_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:40:47.975958+00:00
-- url     : https://prove2.me/submissions/6551ab60-832f-4175-9786-80a0153a226d

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Theorems.Thm_levy_foundations_jumpCountLtIff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- Identify the exact left limit at every arrival of a piecewise path. -/
theorem solution
    {x₀ b : ℝ} {T Y : ℕ → ℝ}
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (n : ℕ) :
    Tendsto (LevyFoundations.piecewisePath x₀ b T Y)
      (𝓝[Set.Iio (T n)] (T n))
      (𝓝 (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) := by
  have h_upper : ∀ᶠ u in 𝓝[Set.Iio (T n)] (T n),
      LevyFoundations.jumpCount T u ≤ n := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hnot : ¬ n < LevyFoundations.jumpCount T u := by
      rw [levy_foundations_jumpCountLtIff T hmono htop n u]
      exact not_le.mpr hu
    omega
  have h_lower : ∀ᶠ u in 𝓝[Set.Iio (T n)] (T n),
      n ≤ LevyFoundations.jumpCount T u := by
    cases n with
    | zero => exact Filter.Eventually.of_forall fun _ => Nat.zero_le _
    | succ m =>
      have hmem : Set.Ioi (T m) ∈ 𝓝[Set.Iio (T (m + 1))] (T (m + 1)) :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (hmono (Nat.lt_succ_self m)))
      filter_upwards [hmem] with u hu
      exact (levy_foundations_jumpCountLtIff T hmono htop m u).mpr (le_of_lt hu)
  have h_count : ∀ᶠ u in 𝓝[Set.Iio (T n)] (T n),
      LevyFoundations.jumpCount T u = n := by
    filter_upwards [h_upper, h_lower] with u h1 h2
    omega
  have h_at : LevyFoundations.jumpCount T (T n) = n + 1 := by
    have h1 : n < LevyFoundations.jumpCount T (T n) :=
      (levy_foundations_jumpCountLtIff T hmono htop n (T n)).mpr le_rfl
    have h2 : ¬ n + 1 < LevyFoundations.jumpCount T (T n) := by
      intro hn
      have he : T (n + 1) ≤ T n :=
        (levy_foundations_jumpCountLtIff T hmono htop (n + 1) (T n)).mp hn
      exact (not_le_of_gt (hmono (Nat.lt_succ_self n))) he
    omega
  set g : ℝ → ℝ := fun u => (x₀ + ∑ i ∈ Finset.range n, Y i) + b * u with hg
  have hval : LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n = g (T n) := by
    simp only [LevyFoundations.piecewisePath, h_at, Finset.sum_range_succ, hg]
    ring
  rw [hval]
  have hgc : Tendsto g (𝓝[Set.Iio (T n)] (T n)) (𝓝 (g (T n))) := by
    have : Continuous g := by fun_prop
    exact this.continuousWithinAt
  refine Filter.Tendsto.congr' ?_ hgc
  filter_upwards [h_count] with u hu
  simp only [LevyFoundations.piecewisePath, hu, hg]
  ring