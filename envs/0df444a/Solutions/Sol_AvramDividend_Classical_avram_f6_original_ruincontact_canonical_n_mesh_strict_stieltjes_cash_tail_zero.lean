-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_ruincontact_canonical_n_mesh_strict_stieltjes_cash_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:26:18.99817+00:00
-- url     : https://prove2.me/submissions/1a0a6609-f2c1-43a9-b82b-a0b2adfa7e51

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
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  let a : ℕ → ℝ := fun j => (T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)
  have ha : Monotone a := by
    intro i j hij
    change (T : ℝ) - (n : ℝ) / ((i : ℝ) + 1) ≤
      (T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)
    have hd : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hij 1
    have hdiv : (n : ℝ) / ((j : ℝ) + 1) ≤
        (n : ℝ) / ((i : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    linarith
  have hzero : Tendsto (fun j : ℕ => (n : ℝ) / ((j : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := (n : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto a atTop (nhds (T : ℝ)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (T : ℝ))).sub hzero
  exact avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
    D hD ω (ruinTime X x D ω) T q hq a ha hlim
