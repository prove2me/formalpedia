-- Prove2me | solution 1 for AvramDividend.Classical.avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:32:00.531137+00:00
-- url     : https://prove2.me/submissions/fc8ce8e9-e136-4cfe-8af6-71b6f07bdf3f

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
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
          ∃ l : ℝ,
            Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
              (𝓝[<] t) (𝓝 l) ∧
            l ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w l| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w l| ≤ KH := by
  classical
  have hband : Set.Icc lower upper ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨lt_of_lt_of_le hlower hy.1, hcap y hy⟩
  obtain ⟨KG, KH, hKG, hKH, hgrad, hhess⟩ :=
    avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
      X hBV hν q hq C w hw lower upper hband
  refine ⟨KG, KH, hKG, hKH, ?_⟩
  intro ω T hclock t ht htT
  obtain ⟨l, hl, ⟨hla, hlb⟩, _, _⟩ :=
    avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
      X x D hD C w hw r lower upper hlower hcap hgrid
      ω T hclock t ht htT
  exact ⟨l, hl, ⟨hla, hlb⟩,
    hgrad t l ⟨hla, hlb⟩, hhess t l ⟨hla, hlb⟩⟩
