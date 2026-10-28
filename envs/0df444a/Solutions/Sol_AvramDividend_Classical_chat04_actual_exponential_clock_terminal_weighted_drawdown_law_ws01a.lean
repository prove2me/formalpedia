-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:22:58.41266+00:00
-- url     : https://prove2.me/submissions/c3a3eaac-6aaf-42e4-824c-5420e2d71a54

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
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
    (r : ℝ) (hr : 0 < r) (c : ℝ) :
    (((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0)).map
      (fun z : Ω × ℝ =>
        runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)) =
    (((P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ =>
        if X.X z.2.toNNReal z.1 - X.X 0 z.1 < c
        then (1 : ℝ≥0∞) else 0)).map
      (fun z : Ω × ℝ =>
        X.X 0 z.1 +
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ z.2.toNNReal ∧ y = X.X s z.1})) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  let T : Ω × ℝ → ℝ := fun z => X.X z.2.toNNReal z.1
  let Z : Ω × ℝ → ℝ := fun z => T z - X.X 0 z.1
  let ρ : Ω × ℝ → ℝ≥0∞ := fun z => if Z z < c then 1 else 0
  let μ : Measure (Ω × ℝ) := (P.prod (expMeasure r)).withDensity ρ
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - T z
  let L : Ω × ℝ → ℝ := fun z =>
    X.X 0 z.1 +
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hD : Measurable D := by simpa only [D, T] using hTri.snd
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hL : Measurable L := hX0.add (by simpa only [] using hTri.fst.snd)
  have hT : Measurable T :=
    (chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hZ : Measurable Z := hT.sub hX0
  have hρ : Measurable ρ := by
    change Measurable (fun z : Ω × ℝ => if Z z < c then (1 : ℝ≥0∞) else 0)
    exact Measurable.ite (measurableSet_Iio.preimage hZ)
      measurable_const measurable_const
  have hμfin : μ Set.univ < ⊤ := by
    change ((P.prod (expMeasure r)).withDensity ρ) Set.univ < ⊤
    rw [withDensity_apply ρ MeasurableSet.univ, Measure.restrict_univ]
    calc
      (∫⁻ z : Ω × ℝ, ρ z ∂(P.prod (expMeasure r))) ≤
          (∫⁻ _ : Ω × ℝ, (1 : ℝ≥0∞) ∂(P.prod (expMeasure r))) :=
        lintegral_mono (fun z => by
          by_cases hz : Z z < c <;> simp [ρ, hz])
      _ = 1 := by simp
      _ < ⊤ := ENNReal.one_lt_top
  letI : IsFiniteMeasure μ := ⟨hμfin⟩
  have hD_evt (d : ℝ) :
      D ⁻¹' Ioi d =
        {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
          T z - X.X s z.1 < -d} := by
    ext z
    change (d < D z) ↔
      ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧ T z - X.X s z.1 < -d
    have hsup := runningSup_gt_level_iff_prior_strict_path_hit
      X z.1 z.2.toNNReal (d + T z)
    constructor
    · intro hd
      have hb : d + T z < runningSup X z.2.toNNReal z.1 := by
        dsimp [D] at hd
        linarith
      obtain ⟨s, hs, hxs⟩ := hsup.mp hb
      exact ⟨s, hs, by dsimp [T] at hxs ⊢; linarith⟩
    · rintro ⟨s, hs, hxs⟩
      have hb : d + T z < X.X s z.1 := by linarith
      have hs' := hsup.mpr ⟨s, hs, by simpa only [T] using hb⟩
      dsimp [D]
      linarith
  have hL_evt (d : ℝ) :
      L ⁻¹' Ioi d =
        {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
          X.X s z.1 - X.X 0 z.1 < -d} := by
    ext z
    change (d < L z) ↔
      ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X s z.1 - X.X 0 z.1 < -d
    have hsurv := chat04_reflected_infimum_Iic_iff_survival
      X z.2.toNNReal z.1 (d - X.X 0 z.1)
    constructor
    · intro hd
      by_contra hnot
      push_neg at hnot
      have hall : ∀ s : ℝ≥0, s ≤ z.2.toNNReal →
          0 ≤ (d - X.X 0 z.1) + X.X s z.1 := by
        intro s hs
        have hn := hnot s hs
        linarith
      have hb := hsurv.mpr hall
      dsimp [L] at hd
      linarith
    · rintro ⟨s, hs, hxs⟩
      by_contra hn
      have hb :
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤
            d - X.X 0 z.1 := by
        dsimp [L] at hn
        linarith
      have hpoint := hsurv.mp hb s hs
      linarith
  have hIoi (d : ℝ) :
      (μ.map D) (Ioi d) = (μ.map L) (Ioi d) := by
    rw [Measure.map_apply hD measurableSet_Ioi, Measure.map_apply hL measurableSet_Ioi]
    rw [hD_evt d, hL_evt d]
    exact chat04_actual_exponential_clock_joint_terminal_reversal_ws01a
      X r hr (-d) c
  have htotal : (μ.map D) Set.univ = (μ.map L) Set.univ := by
    rw [Measure.map_apply hD MeasurableSet.univ, Measure.map_apply hL MeasurableSet.univ]
    simp
  have heq : μ.map D = μ.map L := by
    apply Measure.ext_of_Iic
    intro d
    have hleft : (μ.map D) (Iic d) =
        (μ.map D) Set.univ - (μ.map D) (Ioi d) := by
      simpa only [Set.compl_Ioi] using
        (measure_compl (μ := μ.map D)
          (measurableSet_Ioi : MeasurableSet (Ioi d))
          (measure_ne_top (μ.map D) (Ioi d)))
    have hright : (μ.map L) (Iic d) =
        (μ.map L) Set.univ - (μ.map L) (Ioi d) := by
      simpa only [Set.compl_Ioi] using
        (measure_compl (μ := μ.map L)
          (measurableSet_Ioi : MeasurableSet (Ioi d))
          (measure_ne_top (μ.map L) (Ioi d)))
    rw [hleft, hright, htotal, hIoi d]
  exact heq
