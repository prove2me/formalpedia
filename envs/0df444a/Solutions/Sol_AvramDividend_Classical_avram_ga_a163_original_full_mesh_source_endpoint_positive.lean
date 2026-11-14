-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a163_original_full_mesh_source_endpoint_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:56:35.075206+00:00
-- url     : https://prove2.me/submissions/bca6b938-1838-467e-8c0c-f16f9cc46048

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original Gaussian physical full-cell endpoints remain strictly
positive on the pre-stop band, even when the cell ends exactly at the stop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      (s < ρ ω ∧ s + Δ ≤ ρ ω) →
      0 < x + X.X s ω - rightLimit D s ω ∧
      0 < x + X.X s ω - rightLimit D s ω +
        (X.X (s + Δ) ω - X.X s ω) := by
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hb := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD.1.1 ρ j hprefix
  have hObs := avram_ga_a43_original_clipped_spatial_cell_observations
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix m
  rcases hObs with ⟨_,_,_,hAlt⟩
  filter_upwards [hb,hAlt] with ω hband halt
  intro i hi
  dsimp only
  intro ⟨hs, hle⟩
  have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hden_positive : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hfrac_positive : (0 : ℝ) < 1 / ((j : ℝ) + 1) :=
    one_div_pos.mpr hden_positive
  have hy : 0 < x + X.X (s i) ω - rightLimit D (s i) ω :=
    lt_of_lt_of_le hfrac_positive
      (hband (s i) hs).1
  have hstep : s (i + 1) = s i + Δ := by
    dsimp [s]
    push_cast
    ring
  have h1 : min (s i) (ρ ω) = s i := min_eq_left (le_of_lt hs)
  have h2 : min (s (i + 1)) (ρ ω) = s i + Δ := by
    rw [hstep]
    exact min_eq_left hle
  have h1raw :
      min ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (ρ ω) =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) := h1
  have h2raw :
      min (((i + 1 : ℕ) : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (ρ ω) =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) := h2
  have hi' : i ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self m))
  have hz : 0 < x + X.X (s i + Δ) ω - rightLimit D (s i) ω := by
    rcases halt i hi' with heq | hp
    · have he : x + X.X (s i + Δ) ω - rightLimit D (s i) ω =
        x + X.X (s i) ω - rightLimit D (s i) ω := by
        simpa only [s, Δ, h1raw, h2raw] using heq.2
      linarith
    · simpa only [s, Δ, h1raw, h2raw] using hp.2
  exact ⟨hy, by linarith⟩
