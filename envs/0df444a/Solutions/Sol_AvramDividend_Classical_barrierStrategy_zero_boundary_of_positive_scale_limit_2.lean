-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_scale_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:56:40.238991+00:00
-- url     : https://prove2.me/submissions/53fc8cc4-9f43-4af7-90e7-19631d2738d5

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The positive scale-ratio identity plus its boundary limit closes zero-barrier reflection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hlimit : Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      atTop (nhds (barrierValue W 0 0))) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  have hfinite : barrierSupValue X 1 q ≠ ⊤ := by
    have hzero : barrierSupValue X 1 q =
        ENNReal.ofReal (W 1 / deriv W 1) := by
      simpa using hscale 0
    rw [hzero]
    simp
  have hanti : Antitone (fun n : ℕ =>
      ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))) := by
    intro i j hij
    change ENNReal.ofReal (W (1 / ((j : ℝ) + 1)) /
        deriv W (1 / ((j : ℝ) + 1))) ≤
      ENNReal.ofReal (W (1 / ((i : ℝ) + 1)) /
        deriv W (1 / ((i : ℝ) + 1)))
    rw [← hscale j, ← hscale i]
    apply barrierSupValue_mono_barrier X _ _ q
    apply one_div_le_one_div_of_le (by positivity)
    have hijreal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact add_le_add_left hijreal 1
  have hENN : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1))))
      atTop (nhds (ENNReal.ofReal (barrierValue W 0 0))) :=
    ENNReal.tendsto_ofReal hlimit
  have hInf : (⨅ n : ℕ,
      ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))) =
      ENNReal.ofReal (barrierValue W 0 0) :=
    iInf_eq_of_tendsto hanti hENN
  calc
    dividendValue X q 0 (barrierStrategy X 0 0) =
        barrierSupValue X 0 q := barrierValue_self_eq_barrierSupValue X q 0
    _ = ⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q :=
      barrierSupValue_zero_eq_iInf_reciprocal_of_finite X q hfinite
    _ = ⨅ n : ℕ,
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))) := by
      congr 1
      funext n
      exact hscale n
    _ = ENNReal.ofReal (barrierValue W 0 0) := hInf
