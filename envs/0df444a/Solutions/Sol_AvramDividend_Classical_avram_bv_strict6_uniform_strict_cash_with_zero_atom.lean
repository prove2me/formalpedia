-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_uniform_strict_cash_with_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:22:02.218341+00:00
-- url     : https://prove2.me/submissions/1304a82f-ac40-4946-b7fb-76985b17fc45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_uniform_strict_cash_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original strict cutoff cash includes precisely its zero-time atom and positive cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 < T) (n : ℕ)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, (u i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (b : ℝ≥0)
    (hb : (b : ℝ) = T - T / ((n : ℝ) + 2)) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      rightLimit D 0 ω +
        ((∑ i ∈ Finset.range n,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) +
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioo (u n : ℝ) (b : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) := by
  have hd : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hhalf : T / ((n : ℝ) + 2) ≤ T / 2 :=
    div_le_div_of_nonneg_left (le_of_lt hT) (by norm_num) hd
  have hbposR : (0 : ℝ) < (b : ℝ) := by
    rw [hb]
    linarith
  have hbpos : (0 : ℝ≥0) < b := by
    exact_mod_cast hbposR
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      rightLimit D 0 ω +
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo (0 : ℝ) (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal :=
        avram_p3_c_bvchain_original_strict_cash_zero_atom_plus_open_real_exact
          X x C D hD w hjump ω q hq b hbpos
    _ = _ := by
      rw [avram_bv_strict6_uniform_strict_cash_partition
        X x C D hD ω q hq T hT n u hu b hb]
