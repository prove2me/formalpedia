-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_boundary_reward_limit_strict_pos_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:26:26.753795+00:00
-- url     : https://prove2.me/submissions/317b9bc8-01bc-4500-a369-c2ed470cae57

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_pos
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- As a positive drawdown cap diverges, the original expected discounted
stopped reflected Stieltjes dividend reward tends to a finite positive limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ L : ENNReal, 0 < L ∧ L < ⊤ ∧
      Tendsto (fun a : ℝ => barrierSupValue X a q) atTop (𝓝 L) := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_wave3_02_standing_uniform_boundary_reward X hX q hq W hW
  let L : ENNReal := ⨆ a : ℝ, barrierSupValue X a q
  have hpos : 0 < L := by
    have hp : 0 < barrierSupValue X 1 q :=
      avram_wave3_02_standing_barrierSupValue_pos
        X hX q hq W hW 1 one_pos
    exact lt_of_lt_of_le hp
      (le_iSup (fun a : ℝ => barrierSupValue X a q) 1)
  have hall : ∀ a : ℝ, barrierSupValue X a q ≤ ENNReal.ofReal C := by
    intro a
    rcases le_total a 0 with ha | ha
    · exact (barrierSupValue_mono_barrier X a 0 q ha).trans
        (hbound 0 (le_refl (0 : ℝ)))
    · exact hbound a ha
  have hfin : L < ⊤ := by
    apply lt_of_le_of_lt (iSup_le hall)
    exact ENNReal.ofReal_lt_top
  have hmono : Monotone (fun a : ℝ => barrierSupValue X a q) := by
    intro a b hab
    exact barrierSupValue_mono_barrier X a b q hab
  exact ⟨L, hpos, hfin, tendsto_atTop_iSup hmono⟩
