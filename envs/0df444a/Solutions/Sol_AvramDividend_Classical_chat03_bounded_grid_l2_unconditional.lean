-- Prove2me | solution 1 for AvramDividend.Classical.chat03_bounded_grid_l2_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:18:01.924891+00:00
-- url     : https://prove2.me/submissions/7717e8a8-53f5-4148-8d32-917961081f83

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_from_measurable_stop
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-!
Unconditional finite-grid L² estimate: all stopped-observable measurability,
integrability and unit exponential-moment prerequisites are discharged from
exact adapted Lévy process, sampled filtration and finite first exit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω)
    (N : ℝ≥0) (hNm : clock m ≤ N) :
    Integrable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (clock (K ω) : ℝ))) *
      W (x + X.X (clock (K ω)) ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  obtain ⟨hZmeas, hTmeas⟩ :=
    chat03_grid_stopped_reserve_time_measurable
      X clock H hH lower upper m K hK
  exact chat03_bounded_grid_l2_from_measurable_stop
    X q hq W hW θ x hθ hψ clock hc hc0
    H hH lower upper m K hK hZmeas hTmeas N hNm