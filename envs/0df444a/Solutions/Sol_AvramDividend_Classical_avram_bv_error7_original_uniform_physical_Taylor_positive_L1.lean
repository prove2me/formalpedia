-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_uniform_physical_Taylor_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:29:25.622206+00:00
-- url     : https://prove2.me/submissions/98628486-12dc-4953-a927-118b87a84e27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The authentic original X/D physical-grid C1 Taylor positive error
vanishes in L1 once a uniform C1 interior cell certificate is available. -/
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
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ m, ∀ᵐ ω ∂P,
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
          else 0
         let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
         let z : ℕ → ℝ := fun i =>
           x + X.X (u m i) ω - rightLimit D (u m i) ω
         let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
         (∀ i, i < k m →
           Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) ∧
         (∀ i, i < k m → |c i| < δ))) →
       (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
       Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
         atTop (nhds (0 : ℝ))) := by
  obtain ⟨δ, hδ, hBound⟩ :=
    avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom
      X hBV x C D hD w hwC1 hOpen a b hBand q hq T
      u k hGrid Err hSource
  refine ⟨δ, hδ, ?_⟩
  intro hCells
  exact
    avram_bv_error7_original_physical_C1_positive_error_L1_of_variation_bound
      X hX hBV x C D hD w q hq T hT u k Err hSource
      1 (by norm_num) hErrMeas hErrAE (by
        intro m
        simpa only [one_mul] using hBound hCells m)
