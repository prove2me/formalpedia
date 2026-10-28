-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_ratio_and_divergent_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:52:53.6231+00:00
-- url     : https://prove2.me/submissions/6547988e-1d73-4905-9a46-d6505b6aa557

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_scale_limit
import Theorems.Thm_AvramDividend_Classical_scale_ratio_reciprocal_tendsto_of_deriv_atTop
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Diverging right derivative and the positive scale ratios close zero-barrier reflection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall (fun n : ℕ => by
      change 1 / ((n : ℝ) + 1) ∈ Ioi (0 : ℝ)
      simp only [mem_Ioi]
      positivity)
  have hdseq : Tendsto
      (fun n : ℕ => deriv W (1 / ((n : ℝ) + 1)))
      atTop atTop := hderiv.comp hr
  have hratio : Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      atTop (nhds (0 : ℝ)) :=
    scale_ratio_reciprocal_tendsto_of_deriv_atTop W hcont hdseq
  have hval : barrierValue W 0 0 = 0 :=
    barrierValue_zero_of_derivZeroPlus_top W
      (derivZeroPlus_eq_top_of_right_tendsto_atTop W hderiv)
  rw [← hval] at hratio
  exact barrierStrategy_zero_boundary_of_positive_scale_limit X q W hscale hratio
