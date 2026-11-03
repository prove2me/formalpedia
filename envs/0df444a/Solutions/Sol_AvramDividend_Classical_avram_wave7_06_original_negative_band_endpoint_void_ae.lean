-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_endpoint_void_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:05:43.260035+00:00
-- url     : https://prove2.me/submissions/99574a90-99e7-47aa-b408-f76562b65c29

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P,
      (∀ u : ℝ≥0, 0 < u → u < T →
        ¬ (X.X u ω + 1 / ((n : ℝ) + 1) ≤
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) ↔
      (∀ u : ℝ≥0, u ∈ Ioc 0 T →
        ¬ (X.X u ω + 1 / ((n : ℝ) + 1) ≤
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) := by
  classical
  by_cases hT : 0 < T
  · filter_upwards
      [avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
        X T hT] with ω hNoJump
    constructor
    · intro hOpen u hu
      by_cases huEq : u = T
      · subst u
        intro hJump
        have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · have huLt : u < T := lt_of_le_of_ne hu.2 huEq
        exact hOpen u hu.1 huLt
    · intro hClosed u hu0 huLt
      exact hClosed u ⟨hu0, le_of_lt huLt⟩
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) (zero_le)
    subst T
    apply Filter.Eventually.of_forall
    intro ω
    constructor
    · intro _ u hu
      exact False.elim ((not_lt_of_ge hu.2) hu.1)
    · intro _ u hu0 huLt
      exact False.elim ((not_lt_of_ge (zero_le : (0 : ℝ≥0) ≤ u)) huLt)
