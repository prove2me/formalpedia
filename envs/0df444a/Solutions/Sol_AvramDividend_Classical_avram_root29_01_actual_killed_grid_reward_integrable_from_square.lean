-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_integrable_from_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:47:40.31352+00:00
-- url     : https://prove2.me/submissions/8d7e61ff-169f-43df-951b-62edc332df61

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_square_l2
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_meas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original-Levy lower-history-killed scale reward has an actual first
moment, obtained from its proven original-law second moment. -/
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
    Integrable (B.indicator (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let B : Set Ω := {ω | ∀ t : ℝ≥0,
    t ≤ clock (K ω) → 0 ≤ x + X.X t ω}
  let R : Ω → ℝ := fun ω =>
    Real.exp (-(q * (clock (K ω) : ℝ))) *
      W (x + X.X (clock (K ω)) ω)
  have hMeas : Measurable (B.indicator R) := by
    simpa only [B, R] using
      (avram_root29_01_actual_killed_grid_reward_meas
        X q W hW x clock H hH lower upper m K hK)
  have hSquare := (avram_root29_01_actual_killed_grid_reward_square_l2
    X q hq W hW θ x hθ hψ clock hc hc0
      H hH lower upper m K hK N hN).1
  change Integrable (fun ω => (B.indicator R ω)^2) P at hSquare
  have hLp : MemLp (B.indicator R) 2 P :=
    (memLp_two_iff_integrable_sq hMeas.aestronglyMeasurable).2 hSquare
  exact hLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
