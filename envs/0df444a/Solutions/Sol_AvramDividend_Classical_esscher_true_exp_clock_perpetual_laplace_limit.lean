-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_exp_clock_perpetual_laplace_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:50:44.567587+00:00
-- url     : https://prove2.me/submissions/3cf7609e-da8f-4564-95e5-91864e4c9f74

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Iio (0 : ℝ)) = 0 ∧
      ∀ β : ℝ, 0 < β →
        Tendsto (fun n : ℕ => ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
            Real.exp (-β * x) * cdf (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) x ∂volume))
          atTop (nhds (ENNReal.ofReal (1 / β) *
             (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν))) := by
  obtain ⟨ν, hνP, hν0, hνcdf, -, -⟩ :=
    esscher_positive_root_perpetual_probability_support_laplace X q φ hq hφ hroot
  set f : Ω × ℝ → ℝ := fun z => -sInf {y : ℝ | ∃ s : ℝ≥0,
    s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} with hf
  have hfm : Measurable f :=
    (levy_running_infimum_joint_time_path_measurable X).comp
      (measurable_snd.real_toNNReal.prodMk measurable_fst)
  set μ : ℕ → Measure ℝ := fun n => Measure.map f ((P.prod (expMeasure (p n))).withDensity
    (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
      (φ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) with hμ
  have hμP : ∀ n, IsProbabilityMeasure (μ n) := fun n =>
    esscher_true_random_clock_reflected_law_probability X φ (p n) hφ.le (hpos n)
  have hCDF : ∀ x : ℝ, Tendsto (fun n : ℕ => μ n (Iic x)) atTop (nhds (ν (Iic x))) := by
    intro x
    have h := esscher_true_joint_clock_cdf_tendsto_perpetual X φ hφ.le x ν (hνcdf x) p hp hpos
    refine h.congr (fun n => ?_)
    simp only [hμ]
    rw [Measure.map_apply hfm measurableSet_Iic]
    rfl
  refine ⟨ν, hνP, hν0, fun β hβ => ?_⟩
  rw [← esscher_probability_weighted_cdf_real_eq_laplace ν hν0 β hβ]
  exact ENNReal.tendsto_ofReal
    (esscher_probability_cdf_limits_imply_weighted_laplace_limits μ ν hμP hCDF β hβ)
