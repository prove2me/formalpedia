-- Prove2me | solution 1 for AvramDividend.Classical.avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:01:43.833182+00:00
-- url     : https://prove2.me/submissions/63940983-0904-4100-a459-a81ec322f8c2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_ruingated_gaussian_C2_coefficients_bounded
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          |(Real.exp (-(q * (t : ℝ))) * deriv w y) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)| ≤ KG ∧
          |(Real.exp (-(q * (t : ℝ))) *
            (if 0 < y ∧ ENNReal.ofReal y < C
             then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)| ≤ KH := by
  classical
  obtain ⟨KG, KH, hKG, hKH, hsource⟩ :=
    avram_f17_original_preexit_ruingated_gaussian_C2_coefficients_bounded
      X hBV hν q hq C w hw x D hD r lower upper hlower hcap hgrid
  refine ⟨KG, KH, hKG, hKH, ?_⟩
  intro ω T hclock t ht htT
  have h := hsource ω T hclock t ht htT
  dsimp at h ⊢
  rcases h with ⟨_, hgrad, hhess⟩
  by_cases hruin : (t : ℝ≥0∞) ≤ ruinTime X x D ω
  · simpa [hruin] using And.intro hgrad hhess
  · simp [hruin, hKG, hKH]
