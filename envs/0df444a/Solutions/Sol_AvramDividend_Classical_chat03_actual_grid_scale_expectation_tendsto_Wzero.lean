-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_grid_scale_expectation_tendsto_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T15:01:04.638997+00:00
-- url     : https://prove2.me/submissions/6408e36b-39d3-4d8b-b20e-554b5e52210c

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_expectation_of_ae_convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Expectation convergence for the genuine measurable bounded hittingBtwn
q-scale values when W vanishes at zero and finite strict passage occurs
before a common horizon. The L2 bound is supplied by an accepted theorem.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (N : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB {t : ℝ≥0 |
        X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (hτN : ∀ᵐ ω ∂P, τ ω < N)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hNm : ∀ n, (m n : ℝ≥0) * mesh n ≤ N)
    (hcap : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, τ ω + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η)
    (H : ℕ → Filtration ℕ mΩ)
    (hH : ∀ n k, H n k = 𝓕 ((k : ℝ≥0) * mesh n))
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hZ : ∀ᵐ ω ∂P,
      Z ω = Real.exp (-(q * (τ ω : ℝ))) *
        W (x + X.X (τ ω) ω)) :
    Integrable Z P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * (((K n ω : ℝ≥0) * mesh n) : ℝ))) *
        W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω) ∂P)
      atTop (𝓝 (∫ ω, Z ω ∂P)) := by
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        Real.exp (-(q * (((K n ω : ℝ≥0) * mesh n) : ℝ))) *
          W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω))
        atTop (𝓝 (Z ω)) := by
    filter_upwards [hτ, hτN, hcap, hZ] with ω hτω hNω hcapω hZω
    rw [hZω]
    exact chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
      X q W hW hzero ω lower upper x (τ ω) N
        hτω hNω mesh hmesh hpos m hcapω K hK
  exact chat03_capped_grid_scale_expectation_of_ae_convergence
    X q hq W hW θ x hθ hψ
    (fun n k => (k : ℝ≥0) * mesh n)
    (by
      intro n j k hjk
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjk)
        (show (0 : ℝ≥0) ≤ mesh n from zero_le))
    (by intro n; simp)
    H hH lower upper m K hK N hNm Z hZm hconv
