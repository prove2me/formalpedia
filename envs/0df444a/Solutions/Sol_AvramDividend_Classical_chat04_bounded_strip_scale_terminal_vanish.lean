-- Prove2me | solution 1 for AvramDividend.Classical.chat04_bounded_strip_scale_terminal_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:13:27.574551+00:00
-- url     : https://prove2.me/submissions/f6cbdec1-4c35-49cc-a24d-d3de076527e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (y : ℕ → ℝ)
    (hy : ∀ n, 0 ≤ y n ∧ y n ≤ a) :
    Tendsto (fun n : ℕ =>
      Real.exp (-(q * (n : ℝ))) * W (y n)) atTop (𝓝 0) := by
  have hmon : MonotoneOn W (Ici 0) := hW.2.2.2.1
  have hWa (n : ℕ) : W (y n) ≤ W a := by
    exact hmon (mem_Ici.mpr (hy n).1)
      (mem_Ici.mpr (le_trans (hy n).1 (hy n).2)) (hy n).2
  have hnonneg (n : ℕ) :
      0 ≤ Real.exp (-(q * (n : ℝ))) * W (y n) := by
    exact mul_nonneg (Real.exp_nonneg _) (hW.2.1 (y n) (hy n).1)
  have hupper (n : ℕ) :
      Real.exp (-(q * (n : ℝ))) * W (y n) ≤
        Real.exp (-(q * (n : ℝ))) * W a := by
    exact mul_le_mul_of_nonneg_left (hWa n) (Real.exp_nonneg _)
  have hqn : Tendsto (fun n : ℕ => q * (n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hq
  have hdiscount :
      Tendsto (fun n : ℕ => Real.exp (-(q * (n : ℝ))))
        atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hqn
  have hupperZero :
      Tendsto (fun n : ℕ => Real.exp (-(q * (n : ℝ))) * W a)
        atTop (𝓝 0) := by
    simpa only [zero_mul] using hdiscount.mul_const (W a)
  exact squeeze_zero hnonneg hupper hupperZero
