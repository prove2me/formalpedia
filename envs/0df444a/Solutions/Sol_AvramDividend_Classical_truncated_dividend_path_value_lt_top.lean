-- Prove2me | solution 1 for AvramDividend.Classical.truncated_dividend_path_value_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:21:31.683074+00:00
-- url     : https://prove2.me/submissions/6116d71b-c3ac-4807-8592-141e8c6d2486

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ∞ := by
  let s : Set ℝ := paymentTimes σ ∩ Iic T
  have hsubset : s ⊆ Ioc (-1 : ℝ) T := by
    intro t ht
    have htpay :
        0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ) := by
      simpa [s, paymentTimes] using ht.1
    have htT : t ≤ T := by
      simpa [s] using ht.2
    exact ⟨by linarith [htpay.1], htT⟩
  have hmono : Monotone (fun r : ℝ => D r.toNNReal ω) :=
    (hD.2.1 ω).comp Real.toNNReal_monotone
  have hIoc_ne :
      dividendMeasure D ω (Ioc (-1 : ℝ) T) ≠ ∞ := by
    unfold dividendMeasure
    rw [dif_pos hmono, StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
    exact ENNReal.ofReal_ne_top
  have hs_ne : dividendMeasure D ω s ≠ ∞ := by
    apply ne_of_lt
    calc
      dividendMeasure D ω s ≤ dividendMeasure D ω (Ioc (-1 : ℝ) T) :=
        measure_mono hsubset
      _ < ∞ := (lt_top_iff_ne_top).2 hIoc_ne
  change (∫⁻ t in s,
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ∞
  apply setLIntegral_lt_top_of_le_nnreal hs_ne
  refine ⟨1, ?_⟩
  intro t ht
  have htpay :
      0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ) := by
    simpa [s, paymentTimes] using ht.1
  apply ENNReal.ofReal_le_one.mpr
  rw [Real.exp_le_one_iff]
  nlinarith [hq, htpay.1]
