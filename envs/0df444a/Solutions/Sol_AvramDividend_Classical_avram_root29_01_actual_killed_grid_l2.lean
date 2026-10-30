-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_killed_grid_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:33:07.070261+00:00
-- url     : https://prove2.me/submissions/b99f01f7-7092-4622-a2b1-9d8e52fbf3c7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_grid_hitting_index_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_random_grid_history_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_scale_square_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_indicated_scale_l2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Original-Levy finite-grid first-exit q-scale square moment with the
actual continuous lower-survival history and no measurability assumptions. -/
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
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2)) P ∧
    (∫ ω, B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) ω ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  let B : Set Ω := {ω | ∀ t : ℝ≥0,
    t ≤ clock (K ω) → 0 ≤ x + X.X t ω}
  have hKm : Measurable K :=
    avram_root29_01_actual_grid_hitting_index_meas
      X clock H hH lower upper m K hK
  have hB : MeasurableSet B :=
    avram_root29_01_actual_random_grid_history_meas
      X x clock K hKm
  have hSq : AEStronglyMeasurable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P :=
    avram_root29_01_two_sided_grid_scale_square_meas
      X q W hW x clock H hH lower upper m K hK
  exact avram_root29_01_two_sided_grid_indicated_scale_l2
    X q hq W hW θ x hθ hψ clock hc hc0
    H hH lower upper m K hK N hN hSq B hB
