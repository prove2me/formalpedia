-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_best_barrier_value_affine_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:22:09.369251+00:00
-- url     : https://prove2.me/submissions/24eb49e1-b7fb-44ed-ae88-02c12b3f91b2

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_value_mono
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_value_ge_initial_capital
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_barrier_supremum_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Complete source-faithful best-constant-barrier valuation growth:
monotonicity in initial capital and an affine two-sided envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧
      MonotoneOn (fun x : ℝ =>
        ⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
          dividendValue X q x (barrierStrategy X x a)) (Ici 0) ∧
      ∀ x : ℝ, 0 ≤ x →
        ENNReal.ofReal x ≤
          (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
            dividendValue X q x (barrierStrategy X x a)) ∧
        (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
            dividendValue X q x (barrierStrategy X x a)) ≤
          ENNReal.ofReal x + ENNReal.ofReal C := by
  obtain ⟨C, hC, hupper⟩ :=
    avram_wave3_02_all_barrier_supremum_bound X hX q hq W hW
  refine ⟨C, hC, ?_, ?_⟩
  · exact avram_wave3_02_best_barrier_value_mono X hX q hq W hW
  · intro x hx
    exact ⟨avram_wave3_02_best_barrier_value_ge_initial_capital
      X hX q hq W hW x hx, hupper x hx⟩
