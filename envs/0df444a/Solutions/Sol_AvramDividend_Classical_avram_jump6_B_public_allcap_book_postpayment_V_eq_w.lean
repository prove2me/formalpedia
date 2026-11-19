-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_public_allcap_book_postpayment_V_eq_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:56:33.637227+00:00
-- url     : https://prove2.me/submissions/4b593d51-7f29-4f8a-b7a4-49351fe5b18c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      V (riskProcess X x D t ω) =
        w (riskProcess X x D t ω) ∧
      V (x + X.X t ω - rightLimit D t ω) =
        w (x + X.X t ω - rightLimit D t ω) := by
  by_cases hTop : C = ⊤
  · intro ω t
    constructor
    · exact hVtop hTop _
    · exact hVtop hTop _
  · have hCap : ENNReal.ofReal C.toReal = C :=
      ENNReal.ofReal_toReal hTop
    have hxc' : ENNReal.ofReal x ≤ ENNReal.ofReal C.toReal := by
      simpa only [hCap] using hxc
    have hD' : IsAdmissibleLe X x (ENNReal.ofReal C.toReal) D := by
      simpa only [hCap] using hD
    intro ω t
    have hCapReal : riskProcess X x D t ω ≤ C.toReal := by
      simpa only [hCap] using
        (avram_p4_e_localise_original_finite_realcap_invariant_all_times
          X x C.toReal ENNReal.toReal_nonneg hxc' D hD' ω t)
    have hDiv : D t ω ≤ rightLimit D t ω :=
      dividendStrategy_le_rightLimit D hD.1.1 ω t
    have hPost : x + X.X t ω - rightLimit D t ω ≤ C.toReal := by
      dsimp [riskProcess] at hCapReal
      linarith only [hCapReal, hDiv]
    constructor
    . rw [hVfinite hTop, if_pos hCapReal]
    . rw [hVfinite hTop, if_pos hPost]
