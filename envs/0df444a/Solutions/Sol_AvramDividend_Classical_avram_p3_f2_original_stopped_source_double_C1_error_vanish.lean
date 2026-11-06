-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_stopped_source_double_C1_error_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:12:22.235185+00:00
-- url     : https://prove2.me/submissions/54cb5ef3-7192-41df-a188-52c1e9f960fc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_inner_band_stopped_discounted_J_commutator_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Both physical original stopped C1 source errors jointly vanish, ready for the exact Stieltjes cash identity. -/
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
    (a b a₀ b₀ : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ha : a < a₀) (hb : b₀ < b)
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
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a₀ b₀) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m → |c m i| < δ) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |(∑ i ∈ Finset.range (n m),
              Real.exp (-q * (u m i : ℝ)) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))) +
              (∑ i ∈ Finset.range (n m),
                Real.exp (-q * (u m i : ℝ)) *
                  (w (z m i + c m i) - w (z m i) -
                    deriv w (z m i) * c m i))| < η := by
  filter_upwards
    [avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish
      X hBV x C D hD w hwC1 hOpen a b hBand q hq,
     avram_p3_f2_original_inner_band_stopped_discounted_J_commutator_vanish
      X hBV x C D hD w hwC1 hOpen a b a₀ b₀ hBand ha hb q hq]
      with ω hTaylor hMixed
  intro J Y T u n z c j hStart hEnd hGrid hYBand hJBand hFine η hη
  have hHalf : 0 < η / 2 := by linarith
  have hTaylorBound := hTaylor T u n hStart hEnd hGrid hYBand hFine
      (η / 2) hHalf
  have hMixedBound := hMixed T u n hStart hEnd hGrid hJBand
      hFine (η / 2) hHalf
  filter_upwards [hTaylorBound, hMixedBound] with m hT hM
  calc
    |(∑ i ∈ Finset.range (n m),
      Real.exp (-q * (u m i : ℝ)) *
        (w (z m i + c m i - j m i) - w (z m i + c m i) -
          w (z m i - j m i) + w (z m i))) +
      (∑ i ∈ Finset.range (n m),
        Real.exp (-q * (u m i : ℝ)) *
          (w (z m i + c m i) - w (z m i) -
            deriv w (z m i) * c m i))| ≤
        |∑ i ∈ Finset.range (n m),
          Real.exp (-q * (u m i : ℝ)) *
            (w (z m i + c m i - j m i) - w (z m i + c m i) -
              w (z m i - j m i) + w (z m i))| +
        |∑ i ∈ Finset.range (n m),
          Real.exp (-q * (u m i : ℝ)) *
            (w (z m i + c m i) - w (z m i) -
              deriv w (z m i) * c m i)| := abs_add_le _ _
    _ < η := by
      simp only [neg_mul] at hT hM ⊢
      linarith
