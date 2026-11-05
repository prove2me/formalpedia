-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:06:48.695316+00:00
-- url     : https://prove2.me/submissions/7c6e95b2-1fec-4e18-94cc-73ab76334c32

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
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
    (u : ℕ → ℝ≥0) (n : ℕ) :
    ∀ ω i, i < n →
      let a := x + X.X (u i) ω - rightLimit D (u i) ω
      let b := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      V b - V a =
        (w b - w a) +
          (if C = ⊤ then 0
           else if b ≤ C.toReal then 0
           else w C.toReal + (b - C.toReal) - w b) := by
  intro ω i hi a b
  have ha :
      V a = w a :=
    (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
      X x C hC hxc w V hVtop hVfinite D hD ω (u i)).2
  by_cases ht : C = ⊤
  · rw [hVtop ht b, ha]
    simp [ht]
  · by_cases hb : b ≤ C.toReal
    · rw [hVfinite ht b, ha]
      simp [ht, hb]
    · rw [hVfinite ht b, ha]
      simp [ht, hb]
