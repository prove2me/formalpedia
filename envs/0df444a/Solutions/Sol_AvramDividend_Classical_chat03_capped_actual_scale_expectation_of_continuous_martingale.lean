-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_actual_scale_expectation_of_continuous_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:31:45.119984+00:00
-- url     : https://prove2.me/submissions/6072f54b-a704-4d40-82f8-2dcd2fad519b

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_actual_scale_expectation_identity_from_continuous_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_initial_expectation_eq
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-!
The Lévy process starts at zero. Therefore the initial expectation
premise in the continuous-martingale finite-horizon bridge is automatic.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
    (clock : ℕ → ℕ → ℝ≥0)
    (hclock : ∀ n k, clock n k = min ((k : ℝ≥0) * mesh n) T)
    (hAdapt : Adapted 𝓕 X.X)
    (hMart : Martingale
      (fun (t : ℝ≥0) ω => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t ω)) 𝓕 P) :
    (∫ ω, Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω) ∂P) = W x := by
  have hclock0 : ∀ n, clock n 0 = 0 := by
    intro n
    rw [hclock n 0]
    simp
  have hInit : ∀ n, (∫ ω,
      Real.exp (-(q * (clock n 0 : ℝ))) *
        W (x + X.X (clock n 0) ω) ∂P) = W x := by
    intro n
    exact chat03_discounted_scale_initial_expectation_eq
      X q x W (clock n) (hclock0 n)
  exact chat03_capped_actual_scale_expectation_identity_from_continuous_martingale
    X q hq W hW hzero θ x hθ hψ lower upper T τ hτ
    mesh hmesh hpos K hK clock hclock hAdapt hMart hInit
