-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:25:50.849035+00:00
-- url     : https://prove2.me/submissions/21a081ae-02fb-4258-b2e4-fed0a12eb3e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- The exact stopped Gaussian drift-centred source increment is genuinely in L2(P). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    MemLp (fun ω => X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) 2 P := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  change MemLp Y 2 P
  obtain ⟨Xrc, hpaths, hc, hsigma, hmeasure⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hFuture : Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      Xrc.X (τ ω + t) ω - Xrc.X (τ ω) ω) :=
    levy_finiteStopping_stoppedFuturePath_measurable Xrc τ hτ
  rw [hpaths] at hFuture
  have hYm : Measurable Y := by
    dsimp [Y]
    exact ((measurable_pi_apply h).comp hFuture).sub measurable_const
  have hEnergy :
      (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤
        ENNReal.ofReal ((h : ℝ) * X.σ ^ 2) := by
    simpa only [Y] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
        X hν τ hτ T hbounded h
  have hFin : (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) < ⊤ :=
    lt_of_le_of_lt hEnergy ENNReal.ofReal_lt_top
  have hEnormEq : (fun ω : Ω => ‖(Y ω) ^ 2‖ₑ) =
      (fun ω => ENNReal.ofReal ((Y ω) ^ 2)) := by
    funext ω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hHas : HasFiniteIntegral (fun ω => (Y ω) ^ 2) P := by
    rw [hasFiniteIntegral_def]
    simpa only [hEnormEq] using hFin
  have hInt : Integrable (fun ω => (Y ω) ^ 2) P :=
    ⟨(hYm.pow_const 2).aestronglyMeasurable, hHas⟩
  exact (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 hInt
