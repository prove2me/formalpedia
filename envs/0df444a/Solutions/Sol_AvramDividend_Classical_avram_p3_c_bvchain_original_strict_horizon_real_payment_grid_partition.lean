-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_real_payment_grid_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:54:58.559071+00:00
-- url     : https://prove2.me/submissions/f734a429-fd88-4dcd-a0f2-4e9cd5ec161e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The source-finite original strict-horizon cash grid partition commutes
exactly with ENNReal.toReal, with no new finiteness assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hgrid : ∀ i, i < n → u i < u (i + 1))
    (b : ℝ≥0) (hfinal : u n < b) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  let F : ℕ → ℝ≥0∞ := fun i => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
    Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  let G : ℝ≥0∞ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  have hClosed := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
    D hD.1.1 ω (ruinTime X x D ω) b q hq
  have hIncl : paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2.2⟩
  have hFin : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hIncl) hClosed
  have hPartition := avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
    X x C D hD ω q hq u n hzero hgrid b hfinal
  change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∑ i ∈ Finset.range n, F i) + G at hPartition
  have hParts : (∑ i ∈ Finset.range n, F i) < ⊤ ∧ G < ⊤ := by
    apply ENNReal.add_lt_top.mp
    rw [← hPartition]
    exact hFin
  have hEach : ∀ i ∈ Finset.range n, F i ≠ ⊤ := by
    intro i hi
    have hle : F i ≤ ∑ j ∈ Finset.range n, F j :=
      Finset.single_le_sum (fun j hj => bot_le) hi
    exact (lt_of_le_of_lt hle hParts.1).ne
  rw [hPartition]
  rw [ENNReal.toReal_add hParts.1.ne hParts.2.ne]
  exact congrArg (· + G.toReal) (ENNReal.toReal_sum hEach)
