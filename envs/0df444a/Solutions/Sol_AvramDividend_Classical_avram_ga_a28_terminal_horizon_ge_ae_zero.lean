-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a28_terminal_horizon_ge_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:07:47.830514+00:00
-- url     : https://prove2.me/submissions/efa39933-cd00-4196-aefc-af9f07c59ebe

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_original_path_terminal_increment_ae
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_horizon_clipped_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_ga_a30_horizon_final_cell_left_strict
import Theorems.Thm_AvramDividend_Classical_avram_ga_a32_compact_translation_vanishing_radius
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
    let F : ℕ → Ω → ℝ := fun m ω =>
      if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
    ∀ᵐ ω ∂P, (n : ℝ≥0) ≤ ρ ω →
      Tendsto (fun m => F m ω) atTop (nhds (0 : ℝ)) := by
  classical
  have hBand := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD.1.1 ρ j hprefix
  have hPath := avram_ga_a27_original_path_terminal_increment_ae X hNuZero (n : ℝ≥0)
  filter_upwards [hBand, hPath] with ω hBandω hPathω
  intro hρ
  let a : ℝ := (1 : ℝ) / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  let t : ℕ → ℝ≥0 := fun m => (m : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
  let y : ℕ → ℝ := fun m => x + X.X (t m) ω - rightLimit D (t m) ω
  let δ : ℕ → ℝ := fun m => X.X (n : ℝ≥0) ω - X.X (t m) ω
  have ha : 0 < a := by dsimp [a]; positivity
  have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
  have hleft (m : ℕ) : t m < (n : ℝ≥0) := by
    simpa only [t] using
      avram_ga_a30_horizon_final_cell_left_strict (n : ℝ≥0) hn0 m
  have hy (m : ℕ) : y m ∈ Icc a b := by
    simpa [Set.mem_Icc, y, a, b] using hBandω (t m) (lt_of_lt_of_le (hleft m) hρ)
  have hwc : ContinuousOn w (Icc (a - a / 2) (b + a / 2)) := by
    apply hw_smooth.continuousOn.mono
    intro z hz
    constructor
    · have hzlo : a - a / 2 ≤ z := hz.1
      linarith
    · simp [hTopCap]
  have hδ : Tendsto δ atTop (nhds (0 : ℝ)) := by simpa [δ, t] using hPathω
  have hwlim := avram_ga_a32_compact_translation_vanishing_radius
    w a b (a / 2) (by linarith) hwc y δ hy hδ
  have hMul : Tendsto (fun m => Real.exp (-(q * (n : ℝ))) *
      (w (y m + δ m) - w (y m))) atTop (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hwlim)
  have hMax : Tendsto (fun m => max (Real.exp (-(q * (n : ℝ))) *
      (w (y m + δ m) - w (y m))) (0 : ℝ)) atTop (nhds (0 : ℝ)) := by
    simpa [max_self] using hMul.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hρpos : (0 : ℝ≥0) < ρ ω := lt_of_lt_of_le hn0 hρ
  have hl (m : ℕ) : min ((m : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)))
      (ρ ω) = t m := min_eq_left (le_trans (le_of_lt (hleft m)) hρ)
  have hr (m : ℕ) : min (((m + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (ρ ω) = (n : ℝ≥0) :=
    avram_ga_a27_horizon_clipped_endpoint (n : ℝ≥0) m (ρ ω) hρ
  convert hMax using 1
  funext m
  dsimp
  simp only [if_pos hρpos]
  rw [hl m, hr m]
  dsimp [t, y, δ]
  congr 3 <;> ring
