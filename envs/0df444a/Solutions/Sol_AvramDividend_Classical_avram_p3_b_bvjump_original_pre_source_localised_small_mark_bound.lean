-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_pre_source_localised_small_mark_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:10:39.95095+00:00
-- url     : https://prove2.me/submissions/88c53d8b-68aa-4539-a643-18de152e368c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- A locally bounded source increment at the actual controlled pre-payment
left-limit reserve, with the original source X and original dividend D. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b δ : ℝ)
    (hδ : 0 ≤ δ) (hLip : LipschitzOnWith K w (Icc a b))
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, Upre p ∈ Icc (a + δ) b) :
    ∀ p ∈ E, ∀ z ∈ Icc (-δ) 0,
      |w (Upre p + z) - w (Upre p)| ≤ (K : ℝ) * |z| := by
  intro p hp z hz
  exact avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
    w K a b δ (Upre p) z hδ hLip (hE p hp) hz
