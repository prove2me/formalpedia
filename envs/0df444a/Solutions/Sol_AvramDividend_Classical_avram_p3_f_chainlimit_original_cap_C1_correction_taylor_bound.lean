-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:31:02.90048+00:00
-- url     : https://prove2.me/submissions/6aa25a46-4d6d-4884-9a18-6d203bb3bd63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ ω i, i < n →
      let a := x + X.X (u i) ω - rightLimit D (u i) ω
      let b := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      (C ≠ ⊤ → C.toReal < b →
        |w b - w C.toReal - deriv w C.toReal * (b - C.toReal)| ≤
          ε * |b - C.toReal|) →
      |(V b - V a) - (w b - w a)| ≤ ε * |b - C.toReal| := by
  intro ω i hi a b hTaylor
  have hcell :
      V b - V a =
        (w b - w a) +
          (if C = ⊤ then 0
           else if b ≤ C.toReal then 0
           else w C.toReal + (b - C.toReal) - w b) := by
    simpa only [a, b] using
      (avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
        X x C hC hxc w V hVtop hVfinite D hD u n ω i hi)
  calc
    |(V b - V a) - (w b - w a)| =
      |if C = ⊤ then 0
       else if b ≤ C.toReal then 0
       else w C.toReal + (b - C.toReal) - w b| := by
         rw [hcell]
         congr 1
         ring
    _ ≤ ε * |b - C.toReal| := by
      by_cases ht : C = ⊤
      · simp only [if_pos ht, abs_zero]
        exact mul_nonneg hε (abs_nonneg _)
      · by_cases hb : b ≤ C.toReal
        · simp only [if_neg ht, if_pos hb, abs_zero]
          exact mul_nonneg hε (abs_nonneg _)
        · have hT := hTaylor ht (lt_of_not_ge hb)
          rw [hSlope ht] at hT
          have heq :
              (if C = ⊤ then 0
               else if b ≤ C.toReal then 0
               else w C.toReal + (b - C.toReal) - w b) =
                -(w b - w C.toReal - (b - C.toReal)) := by
            simp only [if_neg ht, if_neg hb]
            ring
          rw [heq, abs_neg]
          simpa only [one_mul] using hT
