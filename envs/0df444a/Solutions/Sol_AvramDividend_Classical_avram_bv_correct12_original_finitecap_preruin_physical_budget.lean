-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_original_finitecap_preruin_physical_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:32:38.755175+00:00
-- url     : https://prove2.me/submissions/dff2817b-fc32-4bd2-a25a-409f0aaf711f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_closedcap_physical_dividend_budget
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Instantiate the physical dividend budget on every actual pre-ruin finite-cap prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, (T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) →
        ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
          (rightLimit D t ω - rightLimit D s ω) +
            (w (x + X.X t ω - rightLimit D t ω) -
              w (x + X.X s ω - rightLimit D s ω)) ≤
            L * (((t : ℝ) - (s : ℝ)) * X.drift) := by
  classical
  have hb : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hbC : ENNReal.ofReal C.toReal ≤ C := by
    simpa only [ENNReal.ofReal_toReal hFinite] using le_refl C
  obtain ⟨L, hL, hpath⟩ :=
    avram_bv_correct12_finite_activity_closedcap_physical_dividend_budget
      X hX hBV hactivity q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x D hD.1.1 C.toReal hb hbC
  refine ⟨L, hL, ?_⟩
  filter_upwards [hpath] with ω hω
  intro hPre s t hst htT
  have hmem (u : ℝ≥0) (hu : u ≤ T) :
      (u : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
    ⟨u.property, by exact_mod_cast hu⟩
  have hband (u : ℝ≥0) (hu : u ≤ T) :
      x + X.X u ω - rightLimit D u ω ∈ Icc (0 : ℝ) C.toReal := by
    have hu0 : 0 ≤ x + X.X u ω - rightLimit D u ω := by
      simpa using
        (avram_wave5_04b_closed_preruin_actual_postpayment_solvency
          X x C D hD ω T hPre (u : ℝ) (hmem u hu))
    have hcap :=
      capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω u
    have huC : x + X.X u ω - rightLimit D u ω ≤ C.toReal := by
      simpa only [ENNReal.toReal_ofReal hu0] using
        (ENNReal.toReal_mono hFinite hcap)
    exact ⟨hu0, huC⟩
  exact hω s t hst (hband s (hst.trans htT)) (hband t htT)
