-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_dyadic_ceiling_reflected_drawdown_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:12:00.75711+00:00
-- url     : https://prove2.me/submissions/5abeaf53-af71-4c5d-ac87-262807bba2a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let r : ℝ≥0 := (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n
      runningSup X r ω - X.X r ω)
      atTop (𝓝 (runningSup X t ω - X.X t ω)) := by
  let round : ℕ → ℝ≥0 := fun n =>
    (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hround : Tendsto round atTop (𝓝[Ici t] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact dyadic_ceiling_nnreal_tendsto t
    · exact Filter.Eventually.of_forall
        (fun n => dyadic_ceiling_time_ge_nnreal t n)
  have hsup : Tendsto (fun n : ℕ => runningSup X (round n) ω)
      atTop (𝓝 (runningSup X t ω)) :=
    (runningSup_right_continuous_actual X ω t).tendsto.comp hround
  have hpath : Tendsto (fun n : ℕ => X.X (round n) ω)
      atTop (𝓝 (X.X t ω)) :=
    (X.rightCont ω t).tendsto.comp hround
  simpa only [round] using hsup.sub hpath
