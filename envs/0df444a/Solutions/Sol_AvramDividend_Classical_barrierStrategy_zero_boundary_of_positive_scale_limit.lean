-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_scale_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:55:24.116996+00:00
-- url     : https://prove2.me/submissions/1f9cf7fd-fb9f-4e46-a53b-2cba97cbe7ad

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hlimit : Filter.Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (barrierValue W 0 0))) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  have hfin : barrierSupValue X 1 q ≠ ⊤ := by
    have := hscale 0
    norm_num at this
    rw [this]
    exact ENNReal.ofReal_ne_top
  rw [AvramDividend.Classical.barrierValue_self_eq_barrierSupValue,
    AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_finite X q hfin]
  have hanti : Antitone (fun n : ℕ => barrierSupValue X (1 / ((n : ℝ) + 1)) q) := by
    intro n m hnm
    refine AvramDividend.Classical.barrierSupValue_mono_barrier X _ _ q ?_
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have h1 := tendsto_atTop_iInf hanti
  have h2 : Filter.Tendsto (fun n : ℕ => barrierSupValue X (1 / ((n : ℝ) + 1)) q) Filter.atTop
      (nhds (ENNReal.ofReal (barrierValue W 0 0))) := by
    simp_rw [hscale]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hlimit
  exact tendsto_nhds_unique h1 h2
