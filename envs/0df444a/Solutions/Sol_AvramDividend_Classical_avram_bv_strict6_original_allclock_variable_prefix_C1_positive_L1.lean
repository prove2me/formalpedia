-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_original_allclock_variable_prefix_C1_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:31:56.586196+00:00
-- url     : https://prove2.me/submissions/7e49bf53-7c50-46cd-856f-b179218c47d8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_endpoint_C1_mesh_error_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_allclock_BV_mass_positive_DCT
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original X/D/J/Y variable-endpoint physical-grid C1 positive error
vanishes in mean from the authentic uniform source mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m ω i ≤ u m ω (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℝ := fun i => Y (u m ω (i + 1)) - Y (u m ω i)
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m ω i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m ω (i + 1)) - Y (u m ω i)
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hAE :=
    avram_bv_error7_original_variable_endpoint_C1_mesh_error_ae
      X hBV x C D hD w hwC1 hOpen a b hBand q hq T
      u k hGrid Err hSource hPath
  have hCells : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m ω (i + 1)) - Y (u m ω i)
       ∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) := by
    filter_upwards [hPath] with ω hω
    dsimp at hω ⊢
    exact hω.1
  have hUniform : ∀ᵐ ω ∂P, ∀ m,
      ‖Err m ω‖ ≤
        (2 * L) * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) := by
    filter_upwards
      [avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
        X hBV x C D hD w a b L hL hLip hDeriv q hq T, hCells]
      with ω hBound hCellsω
    intro m
    dsimp at hCellsω
    obtain ⟨h0, hT, hmono⟩ := hGrid m ω
    have h := hBound (u m ω) (k m ω) h0 hT hmono (hCellsω m)
    rw [hSource m ω]
    simpa only [Real.norm_eq_abs] using h
  have hDom (m : ℕ) :
      ∀ᵐ ω ∂P, ‖Err m ω‖ ≤
        (2 * L) * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) := by
    filter_upwards [hUniform] with ω hω
    exact hω m
  exact
    avram_bv_strict6_original_allclock_BV_mass_positive_DCT
      X hX hBV T (2 * L) (by positivity)
      Err hErrMeas hAE hDom
