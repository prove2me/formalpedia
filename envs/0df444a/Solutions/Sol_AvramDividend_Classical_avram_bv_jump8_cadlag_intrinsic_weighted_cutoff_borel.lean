-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_cadlag_intrinsic_weighted_cutoff_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:51:24.794272+00:00
-- url     : https://prove2.me/submissions/542f069f-852b-4bc7-94b7-1e7616ced518

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    (k : ℕ) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧ (∀ f, 0 ≤ F f ∧ F f ≤ 1) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        F Y = Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
            (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)))).toReal)) := by
  let g : ℝ → ℝ≥0∞ :=
    fun y => if y < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-y) else 0
  have hg : Measurable g := by
    dsimp [g]
    have hs : MeasurableSet {y : ℝ | y < -(1 / ((k : ℝ) + 1))} :=
      measurableSet_lt measurable_id measurable_const
    have hv : Measurable (fun y : ℝ => ENNReal.ofReal (-y)) := by
      fun_prop
    exact hv.ite hs measurable_const
  obtain ⟨W, hW, hWformula⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel 1 g hg
  refine ⟨fun Y => Real.exp (-((W Y).toReal)), ?_, ?_, ?_⟩
  · exact Real.measurable_exp.comp ((ENNReal.measurable_toReal.comp hW).neg)
  · intro Y
    constructor
    · exact le_of_lt (Real.exp_pos _)
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)
  · intro Y hRC hLL
    change Real.exp (-((W Y).toReal)) = _
    rw [hWformula Y hRC hLL]
    simp only [g, ite_and]
