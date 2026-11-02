-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:01:33.269913+00:00
-- url     : https://prove2.me/submissions/8f6b74d9-1dcf-4d84-b54a-32a4d2495d6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_payment_lintegral_eq_iSup_truncated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
      ⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by
  classical
  let A : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hAmono : Monotone A := by
    intro n m hnm
    apply lintegral_mono_set
    intro t ht
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact ⟨ht.1, le_trans ht.2 hcast⟩
  have hshift : (⨆ n : ℕ, A (n + 1)) = ⨆ n : ℕ, A n := by
    apply le_antisymm
    · exact iSup_le fun n => le_iSup A (n + 1)
    · refine iSup_le fun n => ?_
      exact (hAmono (Nat.le_succ n)).trans
        (le_iSup (fun k : ℕ => A (k + 1)) n)
  have hbase := discounted_payment_lintegral_eq_iSup_truncated
    q (ruinTime X x D ω) (dividendMeasure D ω)
  change (∫⁻ t in paymentTimes (ruinTime X x D ω),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
    ⨆ n : ℕ, A (n + 1)
  exact hbase.trans hshift.symm
