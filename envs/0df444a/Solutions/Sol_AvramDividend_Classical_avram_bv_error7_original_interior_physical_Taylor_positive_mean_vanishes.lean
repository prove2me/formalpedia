-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_interior_physical_Taylor_positive_mean_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:37:51.080623+00:00
-- url     : https://prove2.me/submissions/98fc82af-1f65-4aee-8997-25f7b4e4077b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_physical_C1_error_AE_of_refining_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original X/D compact-interior stopped-grid C1 positive Taylor
error vanishes in mean from physical refinement and intrinsic BV mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hGrid : ∀ m, u m 0 = 0 ∧ u m (k m) = T ∧
      (∀ i, i < k m → u m i ≤ u m (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m (i + 1)) - Y (u m i)
       (∀ m i, i < k m →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m → |c m i| < δ)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hErrAE :=
    avram_bv_error7_original_physical_C1_error_AE_of_refining_grid
      X hBV x C D hD w hwC1 hOpen a b hBand q hq
      T u k hGrid Err hSource hPath
  have hGlobal :=
    avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
      X hBV x C D hD w a b L hL hLip hDeriv q hq T
  have hDom (m : ℕ) :
      ∀ᵐ ω ∂P, ‖Err m ω‖ ≤
        (2 * L) * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) := by
    filter_upwards [hGlobal, hPath] with ω hω hp
    dsimp at hp
    obtain ⟨hCells, _⟩ := hp
    obtain ⟨h0, hT', hmono⟩ := hGrid m
    have h := hω (u m) (k m) h0 hT' hmono (hCells m)
    rw [hSource m ω]
    simpa only [Real.norm_eq_abs] using h
  exact
    avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
      X hX hBV x C D hD w q hq T hT u k Err hSource
      (2 * L) (by positivity) hErrMeas hErrAE hDom
