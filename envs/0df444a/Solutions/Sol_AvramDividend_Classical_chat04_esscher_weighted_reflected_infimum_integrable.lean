-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_reflected_infimum_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:16:07.789102+00:00
-- url     : https://prove2.me/submissions/b922061e-37b8-4179-ba73-a5c5a5dbf4e2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) P := by
  have hM : Integrable (fun ω =>
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) P :=
    esscher_exp_process_integrable X θ hθ t
  have hmax : Measurable (fun ω : Ω =>
      max (0 : ℝ) (-sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ t ∧ y = X.X s ω})) :=
    measurable_const.max (levy_running_infimum_measurable X t)
  have hg : Measurable (fun ω : Ω =>
      Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) :=
    (Real.measurable_exp.comp (hmax.const_mul (-β))).div_const β
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hm : Measurable (fun ω : Ω =>
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) :=
    Real.measurable_exp.comp
      ((hXt.const_mul θ).sub measurable_const)
  have hMajorant := hM.const_mul (1 / β)
  have hpoint : ∀ ω : Ω,
      ‖(Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
        Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)‖ ≤
      (1 / β) * Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
    intro ω
    have hn : 0 ≤ max (0 : ℝ)
      (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) :=
      le_max_left _ _
    have hmul : -β * max (0 : ℝ)
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) hn
    have hexp : Real.exp (-β * max (0 : ℝ)
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) ≤ 1 :=
      Real.exp_le_one_iff.mpr hmul
    have hfactor : 0 ≤ Real.exp (-β * max (0 : ℝ)
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β :=
      div_nonneg (Real.exp_nonneg _) hβ.le
    have hle : Real.exp (-β * max (0 : ℝ)
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β ≤ 1 / β :=
      div_le_div_of_nonneg_right hexp hβ.le
    have hMpos : 0 ≤ Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) :=
      Real.exp_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfactor hMpos)]
    exact mul_le_mul_of_nonneg_right hle hMpos
  exact hMajorant.mono' (hg.mul hm).aestronglyMeasurable
    (Filter.Eventually.of_forall hpoint)
