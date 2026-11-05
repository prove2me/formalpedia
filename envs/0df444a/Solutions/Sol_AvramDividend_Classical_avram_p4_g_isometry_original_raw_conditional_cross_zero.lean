-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_raw_conditional_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:23:49.363613+00:00
-- url     : https://prove2.me/submissions/6b070890-7080-4ab4-8811-035c48370e03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

/-- Raw source-filtration centred L2 future increments are orthogonal to past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (F G : Ω → ℝ)
    (hF : StronglyMeasurable[𝓕 t] F)
    (hFl2 : MemLp F 2 P) (hGl2 : MemLp G 2 P)
    (hGcentred : P[G | 𝓕 t] =ᵐ[P] 0) :
    (∫ ω, F ω * G ω ∂P) = 0 := by
  have hFG : Integrable (fun ω => F ω * G ω) P :=
    hFl2.integrable_mul hGl2
  have hG : Integrable G P := hGl2.integrable one_le_two
  have hpull :
      P[fun ω => F ω * G ω | 𝓕 t] =ᵐ[P]
        fun ω => F ω * (P[G | 𝓕 t]) ω :=
    condExp_mul_of_stronglyMeasurable_left
      (m := 𝓕 t) (μ := P) (f := F) (g := G)
      hF hFG hG
  have hzero :
      P[fun ω => F ω * G ω | 𝓕 t] =ᵐ[P] 0 := by
    filter_upwards [hpull, hGcentred] with ω h1 h2
    simp [h1, h2]
  calc
    (∫ ω, F ω * G ω ∂P) =
        ∫ ω, (P[fun ω => F ω * G ω | 𝓕 t]) ω ∂P :=
          (integral_condExp (𝓕.le t)).symm
    _ = 0 := by rw [integral_congr_ae hzero]; simp
