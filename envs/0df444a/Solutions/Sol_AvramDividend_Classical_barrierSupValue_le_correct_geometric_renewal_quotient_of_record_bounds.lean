-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_correct_geometric_renewal_quotient_of_record_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:42:41.173773+00:00
-- url     : https://prove2.me/submissions/f6c9b0dc-784b-47d3-a2ff-ed82d076f414

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! The upper record budget uses p^n, starting with an undiscounted first cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (hε : 0 ≤ ε) (hp : 0 ≤ p) (hplt : p < 1)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω))
      ≤ (∑' n, w n ω))
    (hstep : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * p ^ n)) :
    barrierSupValue X a q ≤ ENNReal.ofReal (ε / (1 - p)) := by
  have hterm (n : ℕ) : ENNReal.ofReal (ε * p ^ n) =
      ENNReal.ofReal ε * (ENNReal.ofReal p) ^ n := by
    rw [ENNReal.ofReal_mul hε, ENNReal.ofReal_pow hp n]
  have hsum : (∑' n : ℕ, ENNReal.ofReal (ε * p ^ n)) =
      ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hden : 0 < 1 - p := sub_pos.mpr hplt
  have hsub : ENNReal.ofReal (1 - p) = 1 - ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_sub (1 : ℝ) hp
  have hratio : ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ =
      ENNReal.ofReal (ε / (1 - p)) := by
    rw [← hsub, ← ENNReal.ofReal_inv_of_pos hden]
    rw [← ENNReal.ofReal_mul hε, div_eq_mul_inv]
  calc
    barrierSupValue X a q ≤ (∑' n, ∫⁻ ω, w n ω ∂P) :=
      barrierSupValue_le_sum_expected_firstRecord_budgets X a q w hw hbudget
    _ ≤ (∑' n, ENNReal.ofReal (ε * p ^ n)) := ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (ε / (1 - p)) := hsum.trans hratio
