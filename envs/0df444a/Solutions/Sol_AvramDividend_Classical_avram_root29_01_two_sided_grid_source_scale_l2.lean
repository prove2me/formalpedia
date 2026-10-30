-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_two_sided_grid_source_scale_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:26:21.622113+00:00
-- url     : https://prove2.me/submissions/1b73c34a-3197-4b9d-8c07-fa4cd57b594d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_compensated_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_moment_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Real L² bound for the actual source Lévy q-scale at an arbitrary
bounded two-sided observation-grid stop, from genuine stopped moments. -/
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
    (N : ℝ≥0) (hN : ∀ ω, clock (K ω) ≤ N)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P) :
    Integrable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  have hθ2 : 0 ≤ 2 * θ := mul_nonneg (by norm_num) hθ
  have hInt :=
    chat03_two_sided_grid_stopped_compensated_exp_integrable
      X clock hc H hH (2 * θ) hθ2 lower upper m K hK
  have hOne :=
    chat03_two_sided_grid_compensated_exp_moment_one
      X clock hc hc0 H hH (2 * θ) hθ2 lower upper m K hK
  exact chat03_fixed_horizon_scale_l2_bound
    X q hq.le W hW θ x hθ hψ N
    (fun ω => clock (K ω))
    (fun ω => X.X (clock (K ω)) ω)
    hN hMeas hInt hOne
