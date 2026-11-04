-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:16:51.606693+00:00
-- url     : https://prove2.me/submissions/00476841-f53d-4d7d-b8f2-a6a380c6b60d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- Original pre-payment reserve has source-ν integrable nonlinear small
negative increments at every localised time-sample pair. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) :
    ∀ p ∈ E, IntegrableOn (fun z : ℝ => w (Upre p + z) - w (Upre p))
      (Ioo (-1 : ℝ) 0) X.ν := by
  intro p hp
  exact avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
    X hBV w K a b (Upre p) hLip (hE p hp)
