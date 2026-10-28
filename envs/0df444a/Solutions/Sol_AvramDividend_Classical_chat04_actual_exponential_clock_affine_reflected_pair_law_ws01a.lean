-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:01:34.612926+00:00
-- url     : https://prove2.me/submissions/161d058b-9694-43ed-80d7-2fe795112e56

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) :
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (runningSup X z.2.toNNReal z.1 - X.X 0 z.1,
         runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)) =
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (X.X z.2.toNNReal z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1},
         X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1})) := by
  classical
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
  let T : Ω × ℝ → ℝ := fun z => X.X z.2.toNNReal z.1
  let Z : Ω × ℝ → ℝ := fun z => T z - X.X 0 z.1
  let D : Ω × ℝ → ℝ := fun z => runningSup X z.2.toNNReal z.1 - T z
  let L : Ω × ℝ → ℝ := fun z => X.X 0 z.1 +
    -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let F : ℝ × ℝ → ℝ × ℝ := fun w => (w.1 + w.2, w.1)
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hD : Measurable D := by simpa only [D, T] using hTri.snd
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) := (X.adapted.measurable).comp measurable_fst
  have hL : Measurable L := hX0.add (by simpa only [] using hTri.fst.snd)
  have hT : Measurable T := (chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hZ : Measurable Z := hT.sub hX0
  have hmD : Measurable (fun z : Ω × ℝ => (D z, Z z)) := hD.prodMk hZ
  have hmL : Measurable (fun z : Ω × ℝ => (L z, Z z)) := hL.prodMk hZ
  have hF : Measurable F := (measurable_fst.add measurable_snd).prodMk measurable_fst
  have hJoint : μ.map (fun z => (D z, Z z)) = μ.map (fun z => (L z, Z z)) := by
    simpa only [μ, D, L, Z, T] using
      (chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a X r hr)
  have hAffine :
      μ.map (F ∘ fun z => (D z, Z z)) =
      μ.map (F ∘ fun z => (L z, Z z)) := by
    calc
      μ.map (F ∘ fun z => (D z, Z z)) =
          (μ.map (fun z => (D z, Z z))).map F :=
        (Measure.map_map hF hmD).symm
      _ = (μ.map (fun z => (L z, Z z))).map F :=
        congrArg (fun ν : Measure (ℝ × ℝ) => ν.map F) hJoint
      _ = μ.map (F ∘ fun z => (L z, Z z)) :=
        Measure.map_map hF hmL
  have hLeft : (F ∘ fun z : Ω × ℝ => (D z, Z z)) =
      (fun z : Ω × ℝ => (runningSup X z.2.toNNReal z.1 - X.X 0 z.1,
        runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)) := by
    funext z
    apply Prod.ext
    · dsimp [F, D, Z, T, Function.comp_def]; ring
    · rfl
  have hRight : (F ∘ fun z : Ω × ℝ => (L z, Z z)) =
      (fun z : Ω × ℝ => (X.X z.2.toNNReal z.1 +
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1},
       X.X 0 z.1 +
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ y = X.X s z.1})) := by
    funext z
    apply Prod.ext
    · dsimp [F, L, Z, T, Function.comp_def]; ring
    · rfl
  rw [hLeft, hRight] at hAffine
  exact hAffine
