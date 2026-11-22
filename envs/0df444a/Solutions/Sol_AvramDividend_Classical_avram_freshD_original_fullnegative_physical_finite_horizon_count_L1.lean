-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:58:59.607218+00:00
-- url     : https://prove2.me/submissions/5c37a2cb-46a5-45ad-aea9-05fe1ad87b78

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let N : Ω → ℝ := fun ω =>
      ((NX ω) (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal
    Integrable N P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro NX N
  have hSquare : Integrable (fun ω => (N ω)^2) P := by
    simpa only [N, NX] using
      (avram_anoise18_original_total_negative_count_finite_activity_L2
        X hFinite (n : ℝ≥0)).1
  obtain ⟨K, hKm, hKeq⟩ :=
    avram_a20_original_negative_borel_nat_count_realisation
      X hFinite (n : ℝ≥0) (Iio (0 : ℝ))
      measurableSet_Iio (Subset.rfl)
  have hAE : ∀ᵐ ω ∂P, (K ω : ℝ) = N ω := by
    simpa only [N, NX] using hKeq
  have hFmeas : AEStronglyMeasurable N P := by
    have hCast : Measurable (fun j : ℕ => (j : ℝ)) := by
      fun_prop
    have hKmReal : Measurable (fun ω => (K ω : ℝ)) :=
      hCast.comp hKm
    exact hKmReal.aestronglyMeasurable.congr hAE
  have hDom : Integrable (fun ω => (N ω)^2 + 1) P :=
    hSquare.add (integrable_const 1)
  apply Integrable.mono' hDom hFmeas
  filter_upwards [] with ω
  have hN : 0 ≤ N ω := ENNReal.toReal_nonneg
  have hsq : 0 ≤ (N ω - 1)^2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hN]
  nlinarith
