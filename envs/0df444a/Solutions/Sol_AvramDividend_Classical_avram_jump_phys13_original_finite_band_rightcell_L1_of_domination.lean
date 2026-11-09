-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T01:24:53.315438+00:00
-- url     : https://prove2.me/submissions/16dd43b1-738c-45b2-bae7-f8f577be691d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A dominated physical original-jump final-cell error vanishes in L1 at each fixed negative cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω)))
    (F : ℕ → Ω → ℝ)
    (hFvanish : ∀ k ω,
      {u : ℝ≥0 | τ ω < u ∧ u ≤ e k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((cut : ℝ) + 1))} = ∅ → F k ω = 0)
    (hFmeas : ∀ k, AEStronglyMeasurable (fun ω => |F k ω|) P)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, |F k ω| ≤ B ω) :
    Tendsto (fun k => ∫ ω, |F k ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
  have hPoint (ω : Ω) :
      Tendsto (fun k => |F k ω|) atTop (𝓝 (0 : ℝ)) := by
    have hVoid :=
      avram_jump_phys13_original_finite_cutoff_rightcell_eventually_void
        X ω T cut (τ ω) (fun k => e k ω)
        (fun k => heBound k ω) (heTendsto ω)
    have hZero : ∀ᶠ k in atTop, |F k ω| = (0 : ℝ) := by
      filter_upwards [hVoid] with k hk
      simp [hFvanish k ω hk]
    exact tendsto_nhds_of_eventually_eq hZero
  have hBoundNorm :
      ∀ k, ∀ᵐ ω ∂P, ‖|F k ω|‖ ≤ B ω := by
    intro k
    filter_upwards [hDom k] with ω hω
    simpa [Real.norm_eq_abs, abs_abs] using hω
  have hL1 :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      B hFmeas hBI hBoundNorm (Filter.Eventually.of_forall hPoint)
  simpa using hL1
