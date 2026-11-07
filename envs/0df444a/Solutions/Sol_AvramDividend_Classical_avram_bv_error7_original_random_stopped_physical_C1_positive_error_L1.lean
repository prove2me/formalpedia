-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_random_stopped_physical_C1_positive_error_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:13:11.957667+00:00
-- url     : https://prove2.me/submissions/e6eac4cd-e658-4305-b7da-1ded8dc1bb83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_endpoint_C1_positive_error_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_random_stopped_physical_Taylor_error_AE_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_prefix_eq_masked_finite_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Under an original measurable stopped index and exact original source,
the positive BV C1 Taylor error on the physical grid vanishes in mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hwMeas : Measurable w)
    (hDerivMeas : Measurable (deriv w))
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
    (u : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (k : ℕ → Ω → ℕ) (hk : ∀ m, Measurable (k m))
    (hBound : ∀ m ω, k m ω ≤ N m)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1)))
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
       ∑ i ∈ Finset.range (N m),
         if i < k m ω then
           Real.exp (-(q * (u m i : ℝ))) *
             (w (z i + c i) - w (z i) - deriv w (z i) * c i)
         else 0))
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
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ))) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hMeas : ∀ m, AEStronglyMeasurable (Err m) P :=
    avram_bv_error7_original_random_stopped_physical_Taylor_error_AE_measurable
      X hX hBV x C D hD w hwMeas hDerivMeas q u N k hk Err hSource
  have hSource' (m : ℕ) (ω : Ω) : Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)) := by
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u m i) ω - rightLimit D (u m i) ω
    let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
    have hs : Err m ω =
        ∑ i ∈ Finset.range (N m), if i < k m ω then
          Real.exp (-(q * (u m i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)
        else 0 := by
      simpa only [z, c, Y, J] using hSource m ω
    exact hs.trans (avram_bv_error7_stopped_prefix_eq_masked_finite_grid
      (N m) (k m ω) (hBound m ω)
      (fun i => Real.exp (-(q * (u m i : ℝ))) *
        (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
  exact avram_bv_error7_original_variable_endpoint_C1_positive_error_L1
    X hX hBV x C D hD w hwC1 hOpen a b hBand
    L hL hLip hDeriv q hq T hT
    (fun m (_ : Ω) i => u m i) k hGrid
    Err hSource' hPath hMeas
