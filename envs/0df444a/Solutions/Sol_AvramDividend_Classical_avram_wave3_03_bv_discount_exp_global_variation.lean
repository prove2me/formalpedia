-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discount_exp_global_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:49:04.524829+00:00
-- url     : https://prove2.me/submissions/dd8a81a9-924e-471c-af6b-7cfedd6640d3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Nonnegative discount rates give a globally bounded-variation discount
    factor on the original nonnegative time axis. -/
theorem solution (q : ℝ) (hq : 0 ≤ q) :
    BoundedVariationOn
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) Set.univ := by
  have hexpmono : MonotoneOn Real.exp (Iic (0 : ℝ)) := by
    intro a ha b hb hab
    exact Real.exp_le_exp.mpr hab
  have hexpbound : ∀ z ∈ Iic (0 : ℝ), |Real.exp z| ≤ (1 : ℝ) := by
    intro z hz
    rw [abs_of_pos (Real.exp_pos z)]
    simpa using (Real.exp_le_exp.mpr hz : Real.exp z ≤ Real.exp 0)
  have hexpbv : BoundedVariationOn Real.exp (Iic (0 : ℝ)) :=
    hexpmono.boundedVariationOn hexpbound
  have hqneg : -q ≤ 0 := neg_nonpos.mpr hq
  have hanti : AntitoneOn (fun t : ℝ≥0 => -q * (t : ℝ)) Set.univ := by
    intro s hs t ht hst
    have hr : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    exact mul_le_mul_of_nonpos_left hr hqneg
  have hmap : MapsTo (fun t : ℝ≥0 => -q * (t : ℝ)) Set.univ
      (Iic (0 : ℝ)) := by
    intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg hqneg (by positivity)
  have hvariation :
      eVariationOn (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) Set.univ ≤
        eVariationOn Real.exp (Iic (0 : ℝ)) := by
    simpa only [Function.comp_def] using
      (eVariationOn.comp_le_of_antitoneOn Real.exp
        (fun t : ℝ≥0 => -q * (t : ℝ)) hanti hmap)
  exact ne_top_of_le_ne_top hexpbv hvariation
