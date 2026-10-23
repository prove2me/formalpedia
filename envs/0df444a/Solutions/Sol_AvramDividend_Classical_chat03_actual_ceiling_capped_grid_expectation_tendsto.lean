-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_expectation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:01:55.041511+00:00
-- url     : https://prove2.me/submissions/867a86ea-2c2a-4a44-ae5c-aeba423e64ed

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_ae_all_branches
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_expectation_of_ae_convergence
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
/-! Finite-horizon stopped q-scale expectation convergence, including terminal ties. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (hZ : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P) :
    Integrable (fun ω =>
      Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω,
        Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω) ∂P)) := by
  let clock : ℕ → ℕ → ℝ≥0 :=
    fun n k => min ((k : ℝ≥0) * mesh n) T
  let Z : Ω → ℝ := fun ω =>
    Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω)
  have hc : ∀ n, Monotone (clock n) := by
    intro n
    exact (chat03_clipped_grid_clock_bounded T (mesh n)).1
  have hc0 : ∀ n, clock n 0 = 0 := by
    intro n
    simp [clock]
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
  have hNm : ∀ n, clock n (Nat.ceil (T / mesh n)) ≤ T := by
    intro n
    exact (chat03_clipped_grid_clock_bounded T (mesh n)).2.2 _
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => Real.exp (-(q * (clock n (K n ω) : ℝ))) *
        W (x + X.X (clock n (K n ω)) ω)) atTop (𝓝 (Z ω)) :=
    chat03_actual_ceiling_capped_grid_scale_ae_all_branches
      X q W hW hzero lower upper x T τ hτ mesh hmesh hpos K hK
  simpa only [clock, Z, NNReal.coe_min, NNReal.coe_mul] using
    (chat03_capped_grid_scale_expectation_of_ae_convergence
      X q hq W hW θ x hθ hψ clock hc hc0 H hHc
      lower upper (fun n => Nat.ceil (T / mesh n)) K hKc
      T hNm Z hZ hconv)
