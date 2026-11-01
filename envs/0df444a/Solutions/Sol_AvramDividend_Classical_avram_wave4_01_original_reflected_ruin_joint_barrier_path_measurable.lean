-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_joint_barrier_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:18:18.538262+00:00
-- url     : https://prove2.me/submissions/1d66af87-2753-468b-8d68-a72f32fafeb1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
import Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The actual strict reflected ruin clock is Borel in barrier and source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun p : ℝ × Ω => barrierRuinTime X p.1 p.2) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hX (j : ℕ) :
      Measurable (fun p : ℝ × Ω => X.X (samples j) p.2) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (measurable_const.prodMk measurable_snd)
  have hSup (j : ℕ) :
      Measurable (fun p : ℝ × Ω => runningSup X (samples j) p.2) :=
    (levy_runningSup_joint_time_path_measurable X).comp
      (measurable_const.prodMk measurable_snd)
  have hEach (j : ℕ) : Measurable (fun p : ℝ × Ω =>
      if X.X (samples j) p.2 - runningSup X (samples j) p.2 < -p.1
      then (samples j : ℝ≥0∞) else ⊤) := by
    exact Measurable.ite
      (measurableSet_lt ((hX j).sub (hSup j)) measurable_fst.neg)
      measurable_const measurable_const
  have hCount : Measurable (fun p : ℝ × Ω =>
      ⨅ j : ℕ,
        if X.X (samples j) p.2 - runningSup X (samples j) p.2 < -p.1
        then (samples j : ℝ≥0∞) else ⊤) :=
    Measurable.iInf hEach
  have hClock (p : ℝ × Ω) :
      barrierRuinTime X p.1 p.2 =
        (⨅ j : ℕ,
          if X.X (samples j) p.2 - runningSup X (samples j) p.2 < -p.1
          then (samples j : ℝ≥0∞) else ⊤) := by
    have hsource :=
      avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
        X p.1 p.2
    have hgrid := reflectedRuin_strictClock_eq_countableSchedule
      X p.2 p.1
    exact hsource.trans (by simpa only [samples, ENNReal.coe_mul] using hgrid)
  have heq :
      (fun p : ℝ × Ω =>
        ⨅ j : ℕ,
          if X.X (samples j) p.2 - runningSup X (samples j) p.2 < -p.1
          then (samples j : ℝ≥0∞) else ⊤) =
      (fun p : ℝ × Ω => barrierRuinTime X p.1 p.2) := by
    funext p
    exact (hClock p).symm
  rw [← heq]
  exact hCount
