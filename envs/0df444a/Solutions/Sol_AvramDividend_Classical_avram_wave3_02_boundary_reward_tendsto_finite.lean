-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_boundary_reward_tendsto_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:14:57.363203+00:00
-- url     : https://prove2.me/submissions/d1951d21-075b-4d0e-835d-6c7fdc916de8

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The true killed Stieltjes reflected reward converges to a finite
limit as the drawdown barrier tends to infinity under Standing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ L : ENNReal, L < ⊤ ∧
      Tendsto (fun a : ℝ => barrierSupValue X a q) atTop (𝓝 L) := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_wave3_02_standing_uniform_boundary_reward X hX q hq W hW
  let L : ENNReal := ⨆ a : ℝ, barrierSupValue X a q
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
  refine ⟨L, hfin, ?_⟩
  exact tendsto_atTop_iSup hmono
