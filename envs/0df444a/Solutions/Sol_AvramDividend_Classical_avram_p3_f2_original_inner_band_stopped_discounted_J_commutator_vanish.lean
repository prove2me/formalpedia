-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_inner_band_stopped_discounted_J_commutator_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:41:23.414281+00:00
-- url     : https://prove2.me/submissions/11b3813f-9c68-4d55-bd3c-9d9ddeb96831

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_inner_band_uniform_C1_J_commutator
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_mixed_J_commutator_mesh_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Only one strict inner original J-reserve segment band suffices for almost-sure stopped discounted mixed C1 error convergence. -/
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
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a₀ b₀) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m → |c m i| < δ) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-q * (u m i : ℝ)) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by
  have hUniform :=
    avram_p3_f2_original_inner_band_uniform_C1_J_commutator
      X x C D hD w hwC1 hOpen a b a₀ b₀ hBand ha hb
  filter_upwards
    [avram_p3_f2_original_discounted_mixed_J_commutator_mesh_vanish
      X hBV x C D hD w q hq] with ω hLimit
  intro J Y T u n z c j hStart hEnd hGrid hInner hFine η hη
  have hCells :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
          |w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i)| ≤ ε * |j m i| := by
    intro ε hε
    obtain ⟨δ, hδ, hEstimate⟩ := hUniform ε hε
    filter_upwards [hFine δ hδ] with m hm
    exact hEstimate ω (u m) (n m) (hInner m) hm
  exact hLimit T u n hStart hEnd hGrid hCells η hη
