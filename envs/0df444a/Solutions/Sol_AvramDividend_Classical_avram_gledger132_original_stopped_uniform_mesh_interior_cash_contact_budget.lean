-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger132_original_stopped_uniform_mesh_interior_cash_contact_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:07:33.567019+00:00
-- url     : https://prove2.me/submissions/b2a158dd-bfa6-4090-9a21-287a04213562

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
import Theorems.Thm_AvramDividend_Classical_avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
import Theorems.Thm_AvramDividend_Classical_avram_gledger112_original_strict_interior_cell_cash_rate_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger131_strict_uniform_grid_interior_width
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (n m : ℕ) (ρ : ℝ≥0) (hρpos : 0 < ρ) (hρn : ρ ≤ (n : ℝ≥0))
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ → u ≤ riskProcess X x D t ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 2 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) ∧
      (∑ i ∈ Finset.range k,
        Real.exp (-(q * (v (i + 1) : ℝ))) *
          (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
           w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω))) +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ≤
      q * (Δ : ℝ) * Real.exp (q * (n : ℝ)) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  dsimp only
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
  have hgrid := avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
    n m ρ hρn
  have hv : Monotone v := hgrid.1
  have hv0 : v 0 = 0 := hgrid.2.1
  obtain ⟨k, hk, hvk, hstop, hinterior, htail⟩ :=
    avram_gledger110_clipped_first_crossing_strict_prefix_and_tail
      n m ρ hρn hρpos
  have hwidth := avram_gledger131_strict_uniform_grid_interior_width
    n m ρ k hinterior
  have hInterior := avram_gledger112_original_strict_interior_cell_cash_rate_bound
    X x D hD ω (n : ℝ≥0) ρ Δ hρn hρruin u hu hprefix
    v hv hv0 k hvk hinterior (fun i hi => le_of_eq (hwidth i hi))
    q hq w C hTopCap hw0 hw_cont hw_neg hw_grad
  refine ⟨k, hk, hvk, hstop, hinterior, htail, ?_⟩
  rw [Finset.sum_add_distrib] at hInterior
  exact (le_of_eq (add_comm _ _)).trans hInterior
