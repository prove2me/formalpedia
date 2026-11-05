-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_stopped_HJB_residual_signed_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:53:43.784176+00:00
-- url     : https://prove2.me/submissions/96b5f196-d115-415e-90b8-181c3f6e3e6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The actual pre-ruin stopped physical-source correction B is integrably
nonpositive even for a ruin-crossing next grid cell. A separately proved
centred jump-compensator M may be added without changing its mean sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (M B : Ω → ℝ)
    (hB : ∀ ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u i)
      B ω =
        (∑ i ∈ Finset.range n,
          if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u (i + 1) : ℝ) - (u i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range n,
           (if (u i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u i : ℝ))) * deriv w (Z i)
           else 0) * (R (u i) - R (u (i + 1)))))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hMzero : (∫ ω, M ω ∂P) = 0) :
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by
  have hR := avram_p3_bv_original_ruin_stopped_residual_mesh_nonpositive
    X hBV x C D w q hw_grad u n hGrid
  have hH := avram_p3_bv_original_ruin_stopped_HJB_grid_nonpositive
    X x C D w q hw_gen u n hGrid
  have hBpoint : ∀ᵐ ω ∂P, B ω ≤ 0 := by
    filter_upwards [hR] with ω hRω
    dsimp only at hRω
    rw [hB ω]
    exact add_nonpos (hH ω) hRω
  constructor
  · exact hMint.add hBint
  · rw [integral_add hMint hBint, hMzero]
    simpa using (integral_nonpos_of_ae hBpoint)
