-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_random_physical_C1_error_ae_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:25:25.998028+00:00
-- url     : https://prove2.me/submissions/fc38af76-45ba-4c23-940f-5d06f30eca55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original X/D C1 error vanishes almost surely on sample-dependent
physical grids. The pathwise BV mesh lemma is uniform over every grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) = T ∧
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
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ))) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by
  filter_upwards
    [avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish
      X hBV x C D hD w hwC1 hOpen a b hBand q hq, hPath]
    with ω hω hPathω
  dsimp at hω hPathω
  obtain ⟨hBandCells, hRefine⟩ := hPathω
  have h0 (m : ℕ) : u m ω 0 = 0 := (hGrid m ω).1
  have hT (m : ℕ) : u m ω (k m ω) = T := (hGrid m ω).2.1
  have hMono (m i : ℕ) (hi : i < k m ω) :
      u m ω i ≤ u m ω (i + 1) := (hGrid m ω).2.2 i hi
  have hErrors := hω T (fun m i => u m ω i)
    (fun m => k m ω) h0 hT hMono hBandCells hRefine
  apply (Metric.tendsto_atTop).2
  intro η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hErrors η hη)
  refine ⟨N, ?_⟩
  intro m hm
  have h := hN m hm
  rw [hSource m ω]
  simpa only [Real.dist_eq, sub_zero] using h
