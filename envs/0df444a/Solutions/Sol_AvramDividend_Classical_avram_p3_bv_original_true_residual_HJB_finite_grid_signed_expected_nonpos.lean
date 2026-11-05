-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_true_residual_HJB_finite_grid_signed_expected_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:35:02.933072+00:00
-- url     : https://prove2.me/submissions/7485f266-917d-4c5f-8342-d84b759f700b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_weighted_residual_mesh_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_interior_HJB_grid_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Expected sign of the actual original BV residual plus interior HJB
finite-grid correction. The centred original jump term M is kept explicit:
its zero-mean premise is supplied separately by original compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (Z : ℕ → Ω → ℝ) (W : ℕ → Ω → ℝ)
    (hW : ∀ ω (i : ℕ), i < n → 0 ≤ W i ω)
    (M B : Ω → ℝ)
    (hB : ∀ ω,
      B ω =
        (∑ i ∈ Finset.range n,
          if 0 < Z i ω ∧ ENNReal.ofReal (Z i ω) < C then
            Real.exp (-(q * (u i : ℝ))) *
              (X.generator w (Z i ω) - q * w (Z i ω)) *
              ((u (i + 1) : ℝ) - (u i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range n, W i ω * (R (u i) - R (u (i + 1)))))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hMzero : (∫ ω, M ω ∂P) = 0) :
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by
  have hR :=
    avram_p3_bv_original_weighted_residual_mesh_nonpositive
      X hBV u n hGrid W hW
  have hH :=
    avram_p3_bv_original_discounted_interior_HJB_grid_nonpositive
      X w q C hw_gen u n hGrid Z
  have hBpoint : ∀ᵐ ω ∂P, B ω ≤ 0 := by
    filter_upwards [hR] with ω hRω
    rw [hB ω]
    exact add_nonpos (hH ω) hRω
  constructor
  · exact hMint.add hBint
  · rw [integral_add hMint hBint, hMzero]
    simpa using (integral_nonpos_of_ae hBpoint)
