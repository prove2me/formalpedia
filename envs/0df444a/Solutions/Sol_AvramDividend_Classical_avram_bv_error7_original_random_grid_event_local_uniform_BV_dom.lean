-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_random_grid_event_local_uniform_BV_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:41:30.596501+00:00
-- url     : https://prove2.me/submissions/3778f6a5-254c-4b9d-a2e8-2d1f1d2d42af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

/-- On one a.e. path set, the original BV mass uniformly dominates the
sample-dependent physical C1 Taylor error masked to an interior event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) = T ∧
      (∀ i, i < k m ω → u m ω i ≤ u m ω (i + 1)))
    (s : Set Ω)
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
    (hCells : ∀ᵐ ω ∂P, ω ∈ s →
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
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b)) :
    ∀ᵐ ω ∂P, ∀ m,
      ‖if ω ∈ s then Err m ω else 0‖ ≤ (2 * L) * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) := by
  filter_upwards
    [avram_bv_error7_original_global_C1_Taylor_error_le_BV_source_mass
      X hBV x C D hD w a b L hL hLip hDeriv q hq T, hCells]
    with ω hBound hCellsω
  intro m
  by_cases hs : ω ∈ s
  · have hc := hCellsω hs
    dsimp at hc
    obtain ⟨h0, hT, hmono⟩ := hGrid m ω
    have h := hBound (u m ω) (k m ω) h0 hT hmono (hc m)
    rw [hSource m ω]
    simpa only [if_pos hs, Real.norm_eq_abs] using h
  · simp only [if_neg hs, norm_zero]
    positivity
