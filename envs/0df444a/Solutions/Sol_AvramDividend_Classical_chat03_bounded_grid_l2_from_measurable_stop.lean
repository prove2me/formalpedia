-- Prove2me | solution 1 for AvramDividend.Classical.chat03_bounded_grid_l2_from_measurable_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:21:16.195213+00:00
-- url     : https://prove2.me/submissions/04b6fd7d-24ad-4720-867d-802f1842a456

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_moment_one
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-!
Nontrivial finite-grid L² assembly. Remaining assumptions hZmeas and
hTmeas are isolated: no integrability or moment assumptions are introduced.
Those measurable-observable inputs have an independent Mathlib discrete
stopped-process proof route.
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
    (hZmeas : Measurable (fun ω => X.X (clock (K ω)) ω))
    (hTmeas : Measurable (fun ω => (clock (K ω) : ℝ)))
    (N : ℝ≥0) (hNm : clock m ≤ N) :
    Integrable (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (clock (K ω) : ℝ))) *
      W (x + X.X (clock (K ω)) ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  let T : Ω → ℝ≥0 := fun ω => clock (K ω)
  let Z : Ω → ℝ := fun ω => X.X (clock (K ω)) ω
  have hKbd : ∀ ω, K ω ≤ m := by
    intro ω
    rw [hK ω]
    exact hittingBtwn_le ω
  have hTbd : ∀ ω, T ω ≤ N := by
    intro ω
    exact (hc (hKbd ω)).trans hNm
  have hWmeas : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hPayMeas : Measurable (fun ω =>
      (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2) := by
    have he : Measurable (fun ω =>
        Real.exp (-(q * (T ω : ℝ)))) :=
      Real.measurable_exp.comp ((measurable_const.mul hTmeas).neg)
    have hw : Measurable (fun ω => W (x + Z ω)) :=
      hWmeas.comp (measurable_const.add hZmeas)
    exact (he.mul hw).pow_const 2
  have hMomentOne :
      (∫ ω, Real.exp (2 * θ * Z ω -
        (T ω : ℝ) * X.ψ (2 * θ)) ∂P) = 1 := by
    exact chat03_two_sided_grid_compensated_exp_moment_one
      X clock hc hc0 H hH (2 * θ)
      (mul_nonneg (by norm_num) hθ)
      lower upper m K hK
  have hMomentInt : Integrable
      (fun ω => Real.exp (2 * θ * Z ω -
        (T ω : ℝ) * X.ψ (2 * θ))) P := by
    apply Integrable.of_integral_ne_zero
    rw [hMomentOne]
    exact one_ne_zero
  exact chat03_fixed_horizon_scale_l2_bound
    X q hq W hW θ x hθ hψ N T Z hTbd
    hPayMeas.aestronglyMeasurable hMomentInt hMomentOne