-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:02:06.545512+00:00
-- url     : https://prove2.me/submissions/7aa7d3f5-0ced-4007-9529-d8d5c843592e

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_ae_all_branches
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_scale_reward_measurable
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-!
The almost-everywhere limit of measurable clipped-grid stopped q-scale
rewards is itself almost everywhere strongly measurable.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (x lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    AEStronglyMeasurable
      (fun ω => Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P := by
  let clock : ℕ → ℕ → ℝ≥0 :=
    fun n k => min ((k : ℝ≥0) * mesh n) T
  have hc : ∀ n, Monotone (clock n) := by
    intro n
    exact (chat03_clipped_grid_clock_bounded T (mesh n)).1
  classical
  let H : ℕ → Filtration ℕ mΩ := fun n =>
    Classical.choose (chat03_monotone_clock_reindexed_filtration 𝓕 (clock n) (hc n))
  have hHc : ∀ n k, H n k = 𝓕 (clock n k) := fun n k =>
    (Classical.choose_spec
      (chat03_monotone_clock_reindexed_filtration 𝓕 (clock n) (hc n))) k
  have hKc : ∀ n ω, K n ω = hittingBtwn
      (fun k ξ => max (X.X (clock n k) ξ - upper)
        (lower - X.X (clock n k) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) ω := by
    intro n ω
    rw [hK n ω]
    exact chat03_actual_ceiling_capped_grid_clipped_hitting_congr
      X lower upper T (mesh n) (hpos n) ω
  have hm : ∀ n, Measurable (fun ω : Ω =>
      Real.exp (-(q * (clock n (K n ω) : ℝ))) *
        W (x + X.X (clock n (K n ω)) ω)) := by
    intro n
    exact chat03_grid_stopped_scale_reward_measurable
      X q x W hW (clock n) (H n) (hHc n)
      lower upper (Nat.ceil (T / mesh n)) (K n) (hKc n)
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => Real.exp (-(q * (clock n (K n ω) : ℝ))) *
        W (x + X.X (clock n (K n ω)) ω)) atTop
        (𝓝 (Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω))) :=
    chat03_actual_ceiling_capped_grid_scale_ae_all_branches
      X q W hW hzero lower upper x T τ hτ mesh hmesh hpos K hK
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hm n).aestronglyMeasurable) hconv
