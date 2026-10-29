-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_actual_Qp_drawdown_negativeInfimum_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:00:23.91553+00:00
-- url     : https://prove2.me/submissions/a8bd13d6-802d-469e-a602-04afb481667a

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The genuine realised-time Esscher law gives exactly the same terminal
drawdown and negative running-infimum distribution. No Q-infinity law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    Measure.map (fun z : Ω × ℝ =>
      runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X z.2.toNNReal z.1 -
            (z.2.toNNReal : ℝ) * X.ψ θ)))) =
    Measure.map (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X z.2.toNNReal z.1 -
            (z.2.toNNReal : ℝ) * X.ψ θ)))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  let μ : Measure (Ω × ℝ) :=
    (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ)))
  letI : IsProbabilityMeasure μ :=
    chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X θ p hθ hp hJoint
  let T : Ω × ℝ → ℝ := fun z => X.X z.2.toNNReal z.1
  let D : Ω × ℝ → ℝ := fun z => runningSup X z.2.toNNReal z.1 - T z
  let L : Ω × ℝ → ℝ := fun z =>
    X.X 0 z.1 + -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hD : Measurable D := by simpa only [D, T] using hTri.snd
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hL : Measurable L := hX0.add (by simpa only [] using hTri.fst.snd)
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
    exact avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
      X θ p (-d) hp hJoint
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
  simpa only [μ, D, T, L, X.X_zero, zero_add] using heq