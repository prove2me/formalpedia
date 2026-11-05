-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_frozen_source_cap_V_eq_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:53:11.253197+00:00
-- url     : https://prove2.me/submissions/250e6bf1-3c72-42e5-a8fa-65bf68584cdb

import Mathlib
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
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hFrozenCap : ∀ ω i, i < n → C ≠ ⊤ →
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ C.toReal) :
    ∀ ω i, i < n →
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω) =
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω) := by
  intro ω i hi
  have hStart :=
    (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
      X x C hC hxc w V hVtop hVfinite D hD ω (u i)).2
  have hEnd :
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) =
        w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) := by
    by_cases ht : C = ⊤
    · exact hVtop ht _
    · rw [hVfinite ht _]
      simp [hFrozenCap ω i hi ht]
  rw [hEnd, hStart]
