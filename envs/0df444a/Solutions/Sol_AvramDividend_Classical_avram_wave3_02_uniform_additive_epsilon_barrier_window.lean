-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_additive_epsilon_barrier_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:37:05.819326+00:00
-- url     : https://prove2.me/submissions/3a2e4fde-511f-4bd2-908a-015f56a8bbf8

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_approximate_finite_barrier_window

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Uniform additive epsilon barrier approximation for the original
source from its accepted lattice-supremum approximation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → x ≤ R →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) + ENNReal.ofReal ε := by
  obtain ⟨A, hA, hbound⟩ :=
    avram_wave3_02_uniform_approximate_finite_barrier_window
      X hX q hq W hW R ε hR hε
  refine ⟨A, hA, ?_⟩
  intro x hx hxR
  exact (hbound x hx hxR).trans (sup_le (by simp) (by simp))
