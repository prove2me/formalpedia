-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_real_exponential_deficit_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:23:52.303334+00:00
-- url     : https://prove2.me/submissions/c7743c53-aec0-4861-aeae-5f07a9c9be7a

import Theorems.Thm_AvramDividend_Classical_negative_levy_exponential_deficit_tendsto_top
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Integrable real negative-jump deficits diverge when negative activity is infinite. -/
theorem solution
    (ν : Measure ℝ)
    (hsupport : ν (Ici (0 : ℝ)) = 0)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (hInt : ∀ n : ℕ, Integrable
      (fun y : ℝ => 1 - Real.exp ((n : ℝ) * y)) ν) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ, (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop atTop := by 
  have hT := negative_levy_exponential_deficit_tendsto_top ν hsupport hνinf
  have hae : ∀ n : ℕ, ∀ᵐ y ∂ν, 0 ≤ 1 - Real.exp ((n : ℝ) * y) := by
    intro n
    have h0 : ∀ᵐ y ∂ν, y ∉ Ici (0 : ℝ) := (measure_eq_zero_iff_ae_notMem).1 hsupport
    filter_upwards [h0] with y hy
    simp only [mem_Ici, not_le] at hy
    have : (n : ℝ) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hy.le
    linarith [Real.exp_le_one_iff.mpr this]
  have heq : ∀ n : ℕ, (∫ y : ℝ, (1 - Real.exp ((n : ℝ) * y)) ∂ν) =
      (∫⁻ y, ENNReal.ofReal (1 - Real.exp ((n : ℝ) * y)) ∂ν).toReal := fun n =>
    integral_eq_lintegral_of_nonneg_ae (hae n) (hInt n).aestronglyMeasurable
  have hfin : ∀ n : ℕ, (∫⁻ y, ENNReal.ofReal (1 - Real.exp ((n : ℝ) * y)) ∂ν) ≠ ⊤ :=
    fun n => (lintegral_ofReal_ne_top_iff_integrable (hInt n).aestronglyMeasurable (hae n)).2 (hInt n)
  simp_rw [heq]
  rw [tendsto_atTop]
  intro b
  filter_upwards [hT.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := b)))] with n hn
  exact (ENNReal.ofReal_le_iff_le_toReal (hfin n)).1 hn.le
