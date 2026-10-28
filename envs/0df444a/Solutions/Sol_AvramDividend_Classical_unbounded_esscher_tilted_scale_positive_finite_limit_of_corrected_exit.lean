-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:02:53.724737+00:00
-- url     : https://prove2.me/submissions/a0e1bc42-c03d-4710-a05b-21e6cb807d0c

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- A positive, bounded, nondecreasing Esscher scale has a strictly positive finite limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by
  obtain ⟨hmono, C, hC⟩ :=
    unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
      X q hq W hW hnbv φ hφ hroot V hV hExit
  let U : ℝ → ℝ := fun t => V (max t 1)
  have hUmono : Monotone U := by
    intro s t hst
    apply hmono
    · exact lt_of_lt_of_le (by norm_num) (le_max_right s (1 : ℝ))
    · exact lt_of_lt_of_le (by norm_num) (le_max_right t (1 : ℝ))
    · exact max_le_max hst le_rfl
  have hUbound : ∀ t : ℝ, U t ≤ C := by
    intro t
    exact hC (max t 1) (lt_of_lt_of_le (by norm_num) (le_max_right t 1))
  rcases tendsto_atTop_of_monotone hUmono with htop | ⟨L, hL⟩
  · obtain ⟨t, ht⟩ := ((tendsto_atTop.1 htop) (C + 1)).exists
    have htbound := hUbound t
    linarith
  · have hWone : 0 < W 1 :=
      (scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv)
        1 (by norm_num)
    have hUone : 0 < U 1 := by
      change 0 < V (max (1 : ℝ) 1)
      rw [max_self, hV 1 (by norm_num)]
      exact mul_pos (Real.exp_pos _) hWone
    have hUone_le : U 1 ≤ L := by
      apply ge_of_tendsto hL
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact hUmono ht
    refine ⟨L, lt_of_lt_of_le hUone hUone_le, ?_⟩
    apply hL.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simp [U, max_eq_left ht]
