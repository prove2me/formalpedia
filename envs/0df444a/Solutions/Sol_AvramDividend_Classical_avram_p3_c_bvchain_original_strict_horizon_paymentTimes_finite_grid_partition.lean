-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_strict_horizon_paymentTimes_finite_grid_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:37:03.437661+00:00
-- url     : https://prove2.me/submissions/e834bbe4-c4ae-435c-9f00-9037c3e609e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original ruin-stopped strict-horizon Stieltjes cash equals all
right-closed interior cells plus the right-open terminal cell, exactly. -/
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
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  induction n generalizing b with
  | zero => simpa [hzero]
  | succ n ih =>
      have hstep : u n < u (n + 1) := hgrid n (Nat.lt_succ_self n)
      have hprev : ∀ i, i < n → u i < u (i + 1) := by
        intro i hi
        exact hgrid i (Nat.lt_succ_of_lt hi)
      have hbefore : u n < b := lt_trans hstep hfinal
      have hIH := ih hprev b hbefore
      have hSplit :=
        avram_p3_c_bvchain_original_paymentTimes_discounted_open_terminal_partition
          X x C D hD ω q hq (u n) (u (n + 1)) b hstep hfinal
      rw [hIH, hSplit]
      simp only [Finset.sum_range_succ]
      ac_rfl
