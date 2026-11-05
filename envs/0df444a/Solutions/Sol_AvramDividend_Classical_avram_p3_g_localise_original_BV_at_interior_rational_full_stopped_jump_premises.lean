-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_BV_at_interior_rational_full_stopped_jump_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:29:29.689827+00:00
-- url     : https://prove2.me/submissions/271bbd43-b494-4b32-877f-214bbfd0461c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At each physical strict interior reserve point a rational band gives
all original BV stopped-source local jump hypotheses automatically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (T : ℝ≥0) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    ∃ a b : ℚ, 0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
      (a : ℝ) ≤ (b : ℝ) ∧ y ∈ Ioo (a : ℝ) (b : ℝ) ∧
      (let τ : Ω → ℝ≥0 := fun ω =>
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
       let E : Set (ℝ≥0 × Ω) := {p |
         (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
         Function.leftLim
           (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
             Icc (a : ℝ) (b : ℝ)}
       (∀ ω, τ ω ≤ T) ∧
       IsStoppingTime 𝓕.rightCont
         (fun ω => (τ ω : WithTop ℝ≥0)) ∧
       MeasurableSet[𝓕.rightCont.predictable] E ∧
       (∀ p ∈ E, Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
           Icc (a : ℝ) (b : ℝ)) ∧
       (∀ p ∈ E, p.1 ≤ T) ∧
       ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
         (∀ u ∈ Icc ((a : ℝ) / 2) (b : ℝ),
           ∀ v ∈ Icc ((a : ℝ) / 2) (b : ℝ),
           |w u - w v| ≤ L * |u - v|) ∧
         (∀ v : ℝ, v ≤ (b : ℝ) → |w v| ≤ R)) := by
  obtain ⟨a, b, ha, ha2, hab, hyab, hBand⟩ :=
    avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
      C y hy hyC
  have hBundle :=
    avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
      X hBV x C D hD w hwCont hwNeg hwC1
        T (a : ℝ) (b : ℝ) ha hab hBand
  exact ⟨a, b, ha, ha2, hab, hyab, hBundle⟩
