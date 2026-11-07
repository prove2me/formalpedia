-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_uniform_physical_Taylor_norm_source_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:29:08.814906+00:00
-- url     : https://prove2.me/submissions/9a2641de-2fb5-4598-8375-8878c1a029c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine X/D discounted Taylor errors have a uniform pathwise
source-mass bound whenever the original cells share one deterministic
strict-interior C1 refinement radius. No budget theorem is assumed. -/
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
           (w (z i + c i) - w (z i) - deriv w (z i) * c i))) :
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
       ∀ m, ∀ᵐ ω ∂P,
         ‖Err m ω‖ ≤ |X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|) := by
  obtain ⟨δ, hδ, hTaylor⟩ :=
    avram_bv_error7_original_interior_Taylor_error_le_L1_source_mass
      X hBV x C D hD w hwC1 hOpen a b hBand q hq T
      1 (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  intro hCells m
  filter_upwards [hTaylor, hCells m] with ω hω hCell
  obtain ⟨h0, hT, hmono⟩ := hGrid m
  have hErr := hω (u m) (k m) h0 hT hmono hCell.1 hCell.2
  rw [hSource m ω]
  simpa only [Real.norm_eq_abs, one_mul] using hErr
