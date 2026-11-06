-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:48:02.066124+00:00
-- url     : https://prove2.me/submissions/f554e15d-ad87-48c9-96cd-9aabb495346d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_BV_source_mesh_error_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original stopped BV discounted source-grid C1 error tends pathwise to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let z : ℕ → ℕ → ℝ := fun m i =>
          x + X.X (u m i) ω - rightLimit D (u m i) ω
        let c : ℕ → ℕ → ℝ := fun m i =>
          Y (u m (i + 1)) - Y (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m → |c m i| < δ) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i) - w (z m i) -
                  deriv w (z m i) * c m i)| < η := by
  filter_upwards
    [avram_p3_f2_original_discounted_BV_source_mesh_error_budget
      X hBV x C D hD w hwC1 hOpen a b hBand q hq]
      with ω hBudget
  intro J Y T u n z c hStart hEnd hGrid hInside hFine η hη
  let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
  let M : ℝ := |X.drift| * (T : ℝ) + (R T - R 0)
  let B : ℝ := |M| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg M]
  have hSmallEps : 0 < η / B := div_pos hη hB
  obtain ⟨δ, hδ, hEstimate⟩ := hBudget (η / B) hSmallEps
  filter_upwards [hFine δ hδ] with m hm
  have hLocal := hEstimate (u m) (n m)
    (hGrid m) (hInside m) hm
  have hClock :
      |X.drift| * ((u m (n m) : ℝ) - (u m 0 : ℝ)) +
        (R (u m (n m)) - R (u m 0)) = M := by
    simp only [hStart m, hEnd m, NNReal.coe_zero, sub_zero]
    rfl
  have hLocal' :
      |∑ i ∈ Finset.range (n m),
        Real.exp (-(q * (u m i : ℝ))) *
          (w (z m i + c m i) - w (z m i) -
            deriv w (z m i) * c m i)| ≤ (η / B) * M := by
    rw [← hClock]
    exact hLocal
  have hMB : M < B := by
    dsimp [B]
    linarith [le_abs_self M]
  calc
    |∑ i ∈ Finset.range (n m),
      Real.exp (-(q * (u m i : ℝ))) *
        (w (z m i + c m i) - w (z m i) -
          deriv w (z m i) * c m i)| ≤ (η / B) * M := hLocal'
    _ < (η / B) * B := mul_lt_mul_of_pos_left hMB hSmallEps
    _ = η := by field_simp [ne_of_gt hB]
