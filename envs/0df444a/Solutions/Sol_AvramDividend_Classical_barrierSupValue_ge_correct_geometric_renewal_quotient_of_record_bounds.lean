-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_correct_geometric_renewal_quotient_of_record_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:42:50.374152+00:00
-- url     : https://prove2.me/submissions/2d2aa4b8-5924-49a6-801b-41536d6f47e9

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_ge_sum_expected_firstRecord_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! The lower record budget uses p^(n+1), discounting at cell exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε p : ℝ)
    (hε : 0 ≤ ε) (hp : 0 ≤ p) (hplt : p < 1)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hbudget : ∀ᵐ ω ∂P, (∑' n, w n ω) ≤
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)))
    (hstep : ∀ n, ENNReal.ofReal (ε * p ^ (n + 1)) ≤
      (∫⁻ ω, w n ω ∂P)) :
    ENNReal.ofReal (ε * p / (1 - p)) ≤ barrierSupValue X a q := by
  have hterm (n : ℕ) : ENNReal.ofReal (ε * p ^ (n + 1)) =
      ENNReal.ofReal ε * (ENNReal.ofReal p) ^ (n + 1) := by
    rw [ENNReal.ofReal_mul hε, ENNReal.ofReal_pow hp (n + 1)]
  have hsum : (∑' n : ℕ, ENNReal.ofReal (ε * p ^ (n + 1))) =
      ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) := by
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
  have hden : 0 < 1 - p := sub_pos.mpr hplt
  have hsub : ENNReal.ofReal (1 - p) = 1 - ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_sub (1 : ℝ) hp
  have hratio : ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) =
      ENNReal.ofReal (ε * p / (1 - p)) := by
    calc
      ENNReal.ofReal ε * (ENNReal.ofReal p * (1 - ENNReal.ofReal p)⁻¹) =
          ENNReal.ofReal ε * (ENNReal.ofReal p * ENNReal.ofReal ((1 - p)⁻¹)) := by
            rw [← hsub, ← ENNReal.ofReal_inv_of_pos hden]
      _ = ENNReal.ofReal (ε * p / (1 - p)) := by
            rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hε]
            congr 1
            simp only [div_eq_mul_inv]
            ring
  calc
    ENNReal.ofReal (ε * p / (1 - p)) =
        (∑' n, ENNReal.ofReal (ε * p ^ (n + 1))) := (hsum.trans hratio).symm
    _ ≤ (∑' n, ∫⁻ ω, w n ω ∂P) := ENNReal.tsum_le_tsum hstep
    _ ≤ barrierSupValue X a q :=
      barrierSupValue_ge_sum_expected_firstRecord_budgets X a q w hw hbudget
