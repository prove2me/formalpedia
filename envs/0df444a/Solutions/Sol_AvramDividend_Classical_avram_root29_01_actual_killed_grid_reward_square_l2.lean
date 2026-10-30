-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_square_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:04:04.89572+00:00
-- url     : https://prove2.me/submissions/9490daf0-fc20-47e3-9cd8-0aee73e64a44

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_l2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual continuous-history killed reward has the squared-reward moment
bound needed by the accepted uniform-second-moment convergence theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω)
    (N : ℝ≥0) (hN : ∀ ω, clock (K ω) ≤ N) :
    let B : Set Ω := {ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω}
    Integrable (fun ω => (B.indicator (fun η =>
      Real.exp (-(q * (clock (K η) : ℝ))) *
        W (x + X.X (clock (K η)) η)) ω)^2) P ∧
    (∫ ω, (B.indicator (fun η =>
      Real.exp (-(q * (clock (K η) : ℝ))) *
        W (x + X.X (clock (K η)) η)) ω)^2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  let B : Set Ω := {ω | ∀ t : ℝ≥0,
    t ≤ clock (K ω) → 0 ≤ x + X.X t ω}
  let R : Ω → ℝ := fun ω =>
    Real.exp (-(q * (clock (K ω) : ℝ))) *
      W (x + X.X (clock (K ω)) ω)
  have hPointwise : (fun ω => (B.indicator R ω)^2) =
      B.indicator (fun ω => (R ω)^2) := by
    funext ω
    by_cases hω : ω ∈ B
    · simp only [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  obtain ⟨hInt, hBound⟩ :=
    avram_root29_01_actual_killed_grid_l2
      X q hq W hW θ x hθ hψ
      clock hc hc0 H hH lower upper m K hK N hN
  change Integrable (fun ω => (B.indicator R ω)^2) P ∧
      (∫ ω, (B.indicator R ω)^2 ∂P) ≤
        ((X.ψ θ - q)⁻¹)^2 *
          Real.exp (2 * θ * (x + 1) +
            (N : ℝ) * max (X.ψ (2 * θ)) 0)
  rw [hPointwise]
  exact ⟨hInt, hBound⟩
