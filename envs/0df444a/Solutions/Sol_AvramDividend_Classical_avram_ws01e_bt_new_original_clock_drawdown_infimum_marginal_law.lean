-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:24:27.57806+00:00
-- url     : https://prove2.me/submissions/3a246743-5081-49b6-8023-6bfc8163b512

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual original-clock terminal drawdown and centred
negative running infimum have the same complete Borel law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    (P.prod (expMeasure p)).map
      (fun z : Ω × ℝ =>
        runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1) =
    (P.prod (expMeasure p)).map
      (fun z : Ω × ℝ =>
        X.X 0 z.1 +
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ z.2.toNNReal ∧ y = X.X s z.1}) := by
  classical
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure p)
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  let I : Ω × ℝ → ℝ := fun z =>
    X.X 0 z.1 + -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let F1 : Ω × ℝ → ℝ × ℝ := fun z =>
    (runningSup X z.2.toNNReal z.1 - X.X 0 z.1, D z)
  let F2 : Ω × ℝ → ℝ × ℝ := fun z =>
    (X.X z.2.toNNReal z.1 +
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}, I z)
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hD : Measurable D := by simpa only [D] using hTri.snd
  have hI : Measurable I := hX0.add (by
    simpa only [I] using hTri.fst.snd)
  have hT : Measurable (fun z : Ω × ℝ => X.X z.2.toNNReal z.1) :=
    (chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hF1 : Measurable F1 :=
    (hTri.fst.fst.sub hX0).prodMk hD
  have hF2 : Measurable F2 :=
    (hT.add hTri.fst.snd).prodMk hI
  have hPair : μ.map F1 = μ.map F2 := by
    simpa only [μ, F1, F2, D, I] using
      (chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
        X p hp)
  change μ.map D = μ.map I
  calc
    μ.map D = (μ.map F1).map Prod.snd := by
      simpa only [F1, Function.comp_def] using
        (Measure.map_map measurable_snd hF1).symm
    _ = (μ.map F2).map Prod.snd := by rw [hPair]
    _ = μ.map I := by
      simpa only [F2, Function.comp_def] using
        (Measure.map_map measurable_snd hF2)
