-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:18:49.6035+00:00
-- url     : https://prove2.me/submissions/59b5cb17-d814-4724-9d86-860f653b926d

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_finite_secant_and_quotient
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_given_perpetual_cdf_true_joint_laplace_limit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_actual_Qp_drawdown_negativeInfimum_map_law
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_descending_factor_small_rate_limit
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_shifted_positive_derivative_exists
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν ∧ 0 < m ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ β : ℝ, 0 < β →
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) =
          ENNReal.ofReal (m * β / (X.ψ (φ + β) - q))) := by
  classical
  obtain ⟨ν, hνP, hν0, hνCDF, _, _⟩ :=
    esscher_positive_root_perpetual_probability_support_laplace
      X q φ hq hφ hroot
  obtain ⟨m, root, _, hm, hrootPos, hrootEq, hroot0, hratio⟩ :=
    esscher_levy_positive_root_finite_secant_and_quotient
      X q φ hq hφ hroot
  let p : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hp0 : Tendsto p atTop (nhds (0 : ℝ)) := by
    simpa only [p] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpPos (n : ℕ) : 0 < p n := by
    dsimp [p]
    positivity
  have hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hp0, Filter.Eventually.of_forall hpPos⟩
  let R : Ω × ℝ → ℝ := fun z =>
    -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}
  let Q : ℝ → Measure (Ω × ℝ) := fun r =>
    (P.prod (expMeasure r)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
  let μ : ℝ → Measure ℝ := fun r => Measure.map R (Q r)
  have hLaplaceLimit (β : ℝ) (hβ : 0 < β) :
      Tendsto (fun n : ℕ =>
        ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ (p n)))
        atTop (nhds (∫⁻ z : ℝ,
          ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) := by
    simpa only [μ, R, Q] using
      (avram_ws01e_integrator_new_given_perpetual_cdf_true_joint_laplace_limit
        X φ hφ.le ν hνP hν0 hνCDF p hp hpPos β hβ)
  have hfinite (r β : ℝ) (hr : 0 < r) (hβ : 0 < β)
      (hneq : β ≠ root r) :
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ r)) =
      ENNReal.ofReal ((r / root r) *
        ((root r - β) / (r - (X.ψ (φ + β) - q)))) := by
    have hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))) :=
      chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
        X φ (chat04_levy_joint_time_state_measurable X)
    obtain ⟨d, hdPos, hdDeriv⟩ :=
      avram_ws01e_cr_new_shifted_positive_derivative_exists
        X q φ (root r) hq hφ hroot (hrootPos r hr)
    have hMap :=
      avram_ws01e_integrator_new_actual_Qp_drawdown_negativeInfimum_map_law
        X φ r hφ.le hr hJoint
    have hDmeas :=
      (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
    have hpull : (∫⁻ z : ℝ,
        ENNReal.ofReal (Real.exp (-β * z)) ∂(μ r)) =
        (∫⁻ z : Ω × ℝ,
          ENNReal.ofReal (Real.exp (-β *
            (runningSup X (Real.toNNReal z.2) z.1 -
              X.X (Real.toNNReal z.2) z.1))) ∂(Q r)) := by
      change (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂
        (Measure.map R (Q r))) = _
      rw [show Measure.map R (Q r) =
        Measure.map (fun z : Ω × ℝ =>
          runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1) (Q r) from hMap.symm]
      exact lintegral_map (by fun_prop) hDmeas
    rw [hpull]
    simpa only [Q, if_neg hneq] using
      (avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
        X q φ r (root r) d hq hφ hroot hr
        (hrootPos r hr) (hrootEq r hr) hdPos hdDeriv
        hJoint β hβ)
  refine ⟨ν, m, hνP, hm, hνCDF, ?_⟩
  intro β hβ
  let g : ℝ := X.ψ (φ + β) - q
  have hg : 0 < g := sub_pos.mpr
    (levy_psi_root_strictly_above_shift X q φ β hq hφ hβ hroot)
  have hrootReal :
      Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    (tendsto_nhdsWithin_iff.mp hroot0).1
  let D : ℝ → ℝ := fun r =>
    (r / root r) * ((root r - β) / (r - g))
  have hD : Tendsto D (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (m * β / g)) := by
    apply esscher_descending_factor_small_rate_limit
      root D g m β hm hβ hg hrootReal hratio
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hDenn : Tendsto (fun n : ℕ => ENNReal.ofReal (D (p n))) atTop
      (nhds (ENNReal.ofReal (m * β / g))) :=
    (ENNReal.continuous_ofReal.tendsto (m * β / g)).comp (hD.comp hp)
  have hrootSeq : Tendsto (fun n : ℕ => root (p n))
      atTop (nhds (0 : ℝ)) := hrootReal.comp hp
  have hsmall : ∀ᶠ n : ℕ in atTop, root (p n) < β :=
    hrootSeq.eventually (eventually_lt_nhds hβ)
  have heventual : (fun n : ℕ =>
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂(μ (p n)))) =ᶠ[atTop]
      (fun n : ℕ => ENNReal.ofReal (D (p n))) := by
    filter_upwards [hsmall] with n hn
    simpa only [D, g] using
      hfinite (p n) β (hpPos n) hβ (ne_of_gt hn)
  exact tendsto_nhds_unique (hLaplaceLimit β hβ)
    (hDenn.congr' heventual.symm)
