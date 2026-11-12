-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger93_original_interior_real_discounted_contact_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:33:14.428337+00:00
-- url     : https://prove2.me/submissions/4ba69c9f-35fe-4ce4-af94-561200ec057c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
import Theorems.Thm_AvramDividend_Classical_avram_gledger45_global_topcap_monotone_zero_negative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (a b : ℝ≥0) (hab : a ≤ b) (hb : b < ρ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hfinite : dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≠ ⊤) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (b : ℝ))) *
          (w (x + X.X b ω - rightLimit D b ω) -
            w (x + X.X b ω - rightLimit D a ω)) ≤
      q * ((b : ℝ) - (a : ℝ)) *
        (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal := by
  have hgrad (y : ℝ) (hy : 0 < y) : 1 ≤ deriv w y := by
    exact hw_grad y hy (by simp [hTopCap])
  have hc := avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
    X x D hD ω ρ u hu hprefix a b hab hb q hq w hw_cont hgrad
  have hmono : rightLimit D a ω ≤ rightLimit D b ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω) hab
  have hW : 0 ≤ w (x + X.X b ω - rightLimit D a ω) -
      w (x + X.X b ω - rightLimit D b ω) := by
    apply sub_nonneg.mpr
    apply avram_gledger45_global_topcap_monotone_zero_negative
      w C hTopCap hw0 hw_cont hw_neg hw_grad
    linarith
  have hExp : 0 ≤ Real.exp (-(q * (b : ℝ))) := le_of_lt (Real.exp_pos _)
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hδ : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr habR
  have hqδ : 0 ≤ q * ((b : ℝ) - (a : ℝ)) := mul_nonneg hq hδ
  have hLeftFin :
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (w (x + X.X b ω - rightLimit D a ω) -
          w (x + X.X b ω - rightLimit D b ω)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hRightFin :
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hfinite
  have hReal := ENNReal.toReal_le_add hc hLeftFin hRightFin
  rw [ENNReal.toReal_ofReal_mul _ _ hExp,
      ENNReal.toReal_ofReal_mul _ _ hqδ,
      ENNReal.toReal_ofReal hW] at hReal
  linarith
