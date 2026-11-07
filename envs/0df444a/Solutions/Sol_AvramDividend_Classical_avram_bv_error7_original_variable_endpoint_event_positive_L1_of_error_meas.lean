-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_variable_endpoint_event_positive_L1_of_error_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:10:36.94781+00:00
-- url     : https://prove2.me/submissions/d2890f41-748d-4b1e-85a9-69f30a531260

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_endpoint_event_exhaustion_positive_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

/-- The original varying-endpoint stopped physical-grid C1 error has
vanishing positive expectation once interior localisation exhausts the
probability space and the off-event original source bound holds. -/
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
    (a b L : ℕ → ℝ)
    (hBand : ∀ n, Set.Icc (a n) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hL : ∀ n, 0 ≤ L n)
    (hLip : ∀ n, ∀ y ∈ Set.Icc (a n) (b n),
      ∀ z ∈ Set.Icc (a n) (b n),
        |w z - w y| ≤ L n * |z - y|)
    (hDeriv : ∀ n, ∀ y ∈ Set.Icc (a n) (b n),
      |deriv w y| ≤ L n)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m ω i ≤ u m ω (i + 1)))
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
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
    (hPath : ∀ n, ∀ᵐ ω ∂P, ω ∈ s n →
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
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc (a n) (b n)) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hOutside : ∀ n m, ∀ᵐ ω ∂P, ω ∉ s n →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hMaskedMeas (n m : ℕ) :
      AEStronglyMeasurable
        (fun ω => if ω ∈ s n then Err m ω else 0) P := by
    change AEStronglyMeasurable ((s n).indicator (Err m)) P
    exact (hErrMeas m).indicator (hs n)
  have hPosMeas (m : ℕ) :
      AEStronglyMeasurable (fun ω => max (Err m ω) 0) P := by
    have hc : Continuous (fun z : ℝ => max z 0) :=
      continuous_id.max continuous_const
    exact hc.comp_aestronglyMeasurable (hErrMeas m)
  exact avram_bv_error7_original_variable_endpoint_event_exhaustion_positive_L1
    X hX hBV x C D hD w hwC1 hOpen a b L
    hBand hL hLip hDeriv q hq T hT u k hGrid
    s hs hExhaust Err hSource hPath
    hMaskedMeas hPosMeas K hK hOutside
