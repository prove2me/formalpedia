-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_negative_mark_real_count_interval_additivity_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:53:16.472298+00:00
-- url     : https://prove2.me/submissions/949e4c26-b1a0-4d44-98c1-f01c74488ac9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_marked_interval_split
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) (hν : X.ν B < ⊤) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P,
      (NX ω (Ioc s t ×ˢ B)).toReal =
        (NX ω (Ioc s r ×ˢ B)).toReal +
          (NX ω (Ioc r t ×ˢ B)).toReal  := by
  intro NX
  have hFirst : ∀ᵐ ω ∂P, NX ω (Ioc s r ×ˢ B) < ⊤ := by
    simpa only [NX] using
      (avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
        X s r hsr B hB hNeg hν)
  have hSecond : ∀ᵐ ω ∂P, NX ω (Ioc r t ×ˢ B) < ⊤ := by
    simpa only [NX] using
      (avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
        X r t hrt B hB hNeg hν)
  filter_upwards [hFirst, hSecond] with ω hF hS
  have hAdd := avram_p4_b_smalljump_original_marked_interval_split
    X ω s r t hsr hrt B hB
  change NX ω (Ioc s t ×ˢ B) =
    NX ω (Ioc s r ×ˢ B) +
      NX ω (Ioc r t ×ˢ B) at hAdd
  rw [hAdd, ENNReal.toReal_add (ne_of_lt hF) (ne_of_lt hS)]
