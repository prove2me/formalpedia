-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_uniform_strict_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:12:59.029789+00:00
-- url     : https://prove2.me/submissions/107647cc-df35-4fd1-922d-1f9647b6e112

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact strict original cash partition over the positive uniform grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 < T) (n : ℕ)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, (u i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (b : ℝ≥0)
    (hb : (b : ℝ) = T - T / ((n : ℝ) + 2)) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hinc (i : ℕ) :
      T * (i : ℝ) / ((n : ℝ) + 2) <
        T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) := by
    apply div_lt_div_of_pos_right ?_ hden
    apply mul_lt_mul_of_pos_left ?_ hT
    exact_mod_cast Nat.lt_succ_self i
  have hzero : u 0 = 0 := by
    apply Subtype.ext
    change (u 0 : ℝ) = (0 : ℝ)
    simpa using hu 0
  have hgrid : ∀ i, i < n → u i < u (i + 1) := by
    intro i _
    change (u i : ℝ) < (u (i + 1) : ℝ)
    calc
      (u i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2) := hu i
      _ < T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) := hinc i
      _ = (u (i + 1) : ℝ) := (hu (i + 1)).symm
  have hend : T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) =
      T - T / ((n : ℝ) + 2) := by
    have hn : (n : ℝ) + 2 ≠ 0 := ne_of_gt hden
    push_cast
    field_simp [hn] <;> ring
  have hfinal : u n < b := by
    change (u n : ℝ) < (b : ℝ)
    calc
      (u n : ℝ) = T * (n : ℝ) / ((n : ℝ) + 2) := hu n
      _ < T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) := hinc n
      _ = T - T / ((n : ℝ) + 2) := hend
      _ = (b : ℝ) := hb.symm
  exact avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
    X x C D hD ω q hq u n hzero hgrid b hfinal
