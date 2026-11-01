-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:57:41.77095+00:00
-- url     : https://prove2.me/submissions/3891c4f4-4a4e-4b63-a7bc-f459024c1b69

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (S : Set (ℝ × Ω)) (hS : MeasurableSet S) :
    Measurable (fun ω : Ω =>
      ∫⁻ t : ℝ, if (t, ω) ∈ S then
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X t.toNNReal ω -
            rightLimit D t.toNNReal ω) - (t.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω) := by
  obtain ⟨κ, hsf, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hsf
  have htime : Measurable (fun z : ℝ × Ω =>
      (Real.toNNReal z.1, z.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hsource : Measurable (fun z : ℝ × Ω =>
      Real.exp
        (θ * (x + X.X z.1.toNNReal z.2 -
          rightLimit D z.1.toNNReal z.2) -
          (z.1.toNNReal : ℝ) * q)) :=
    (avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
      X x D hD θ q).comp htime
  have hf : Measurable (fun z : ℝ × Ω =>
      if z ∈ S then ENNReal.ofReal
        (Real.exp
          (θ * (x + X.X z.1.toNNReal z.2 -
            rightLimit D z.1.toNNReal z.2) -
            (z.1.toNNReal : ℝ) * q)) else 0) :=
    Measurable.ite hS (ENNReal.measurable_ofReal.comp hsource) measurable_const
  have heq :
      Function.uncurry
        (fun (t : ℝ) (ω : Ω) =>
          if (t, ω) ∈ S then ENNReal.ofReal (Real.exp
            (θ * (x + X.X t.toNNReal ω -
              rightLimit D t.toNNReal ω) -
              (t.toNNReal : ℝ) * q)) else 0) =
      (fun z : ℝ × Ω =>
        if z ∈ S then ENNReal.ofReal (Real.exp
          (θ * (x + X.X z.1.toNNReal z.2 -
            rightLimit D z.1.toNNReal z.2) -
            (z.1.toNNReal : ℝ) * q)) else 0) := by
    funext z
    rcases z with ⟨t, ω⟩
    rfl
  have hf' : Measurable (Function.uncurry
      (fun (t : ℝ) (ω : Ω) =>
        if (t, ω) ∈ S then ENNReal.ofReal (Real.exp
          (θ * (x + X.X t.toNNReal ω -
            rightLimit D t.toNNReal ω) -
            (t.toNNReal : ℝ) * q)) else 0)) := by
    rw [heq]
    exact hf
  have hm := Measurable.lintegral_kernel_prod_left
    (κ := κ)
    (f := fun (t : ℝ) (ω : Ω) =>
      if (t, ω) ∈ S then ENNReal.ofReal (Real.exp
        (θ * (x + X.X t.toNNReal ω -
          rightLimit D t.toNNReal ω) -
          (t.toNNReal : ℝ) * q)) else 0)
    hf'
  simpa only [hκ] using hm
