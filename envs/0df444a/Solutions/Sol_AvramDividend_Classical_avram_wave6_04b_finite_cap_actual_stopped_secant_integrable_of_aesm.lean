-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_finite_cap_actual_stopped_secant_integrable_of_aesm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:42:56.788785+00:00
-- url     : https://prove2.me/submissions/71469f2a-424a-4332-880c-8792f739e8a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_finite_cap_actual_stopped_secant_uniform_point_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- On any actual stopped finite dividend measure, the cap-linear forward
secant correction is automatically L1 once its time measurability is known.
Finite cap bounds the residual, and the genuine Stieltjes measure has finite
closed-horizon mass including the singular-continuous and zero atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (q δ : ℝ) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hMeas : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      ((dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)))) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω) := by
  let A : Set ℝ :=
    paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)
  let μ : Measure ℝ := (dividendMeasure D ω).restrict A
  let f : ℝ → ℝ := fun s =>
    Real.exp (-(q * s)) *
      (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))
  let L : ℝ := (w C.toReal - C.toReal) - w 0
  have hAmeas : MeasurableSet A :=
    (paymentTimes_measurable _).inter measurableSet_Icc
  have hA_sub : A ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro s hs
    exact hs.2
  have hstrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hμfinite : μ Set.univ < ⊤ := by
    calc
      μ Set.univ = (dividendMeasure D ω) A := by simp [μ]
      _ ≤ (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) :=
        measure_mono hA_sub
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hstrategy ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure μ := (isFiniteMeasure_iff μ).2 hμfinite
  change Integrable f μ
  have hAES : AEStronglyMeasurable f μ := hMeas
  apply Integrable.of_bound hAES L
  filter_upwards [ae_restrict_mem hAmeas] with s hs
  exact avram_wave6_04b_finite_cap_actual_stopped_secant_uniform_point_bound
    X x C hC hCfinite q δ hq hδ w V hw_cont hw_smooth hw_grad
    hVfinite D hD ω s hs.1
