-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_ruin_contact_rational_final_strict_cash_tail_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:27:29.8727+00:00
-- url     : https://prove2.me/submissions/cafef76c-a620-4b75-91dc-c1761f64ecb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun n : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((T : ℝ) - 1 / ((n : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  let a : ℕ → ℝ := fun n => (T : ℝ) - 1 / ((n : ℝ) + 1)
  have ha : Monotone a := by
    intro i j hij
    change (T : ℝ) - 1 / ((i : ℝ) + 1) ≤
      (T : ℝ) - 1 / ((j : ℝ) + 1)
    have hden : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      exact_mod_cast Nat.add_le_add_right hij 1
    have hfrac : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hden
    linarith
  have hlim : Tendsto a atTop (nhds (T : ℝ)) := by
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hzero :
        Tendsto (fun n : ℕ => (T : ℝ) - 1 / ((n : ℝ) + 1))
          atTop (nhds ((T : ℝ) - 0)))
  exact avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
    D hD ω (ruinTime X x D ω) T q hq a ha hlim
