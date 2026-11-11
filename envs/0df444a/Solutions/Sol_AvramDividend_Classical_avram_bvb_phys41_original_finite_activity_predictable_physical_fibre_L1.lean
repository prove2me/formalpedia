-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:28:53.830597+00:00
-- url     : https://prove2.me/submissions/f0ad1008-9c8d-4d9a-b9ff-6893fc206c8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys40_original_finite_activity_bounded_predictable_mark_kernel_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite original Levy jump activity and finite predictable time give physical L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (c : ℝ) (hc : 0 ≤ c)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (T : ℝ≥0)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ≤ c) :
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  intro H
  obtain ⟨μ, hμ, hClock, hFubini⟩ :=
    avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini X T
  have hMeas : Measurable[(𝓕.rightCont.predictable).prod inferInstance] H := by
    simpa only [H] using
      (avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
        X x D hD w hw_cont hw_neg q E hEm)
  have hKernel : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
        𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    simpa only [H] using
      (avram_bvb_phys40_original_finite_activity_bounded_predictable_mark_kernel_L1
        X x D hD w hw_cont hw_neg q hq c hc μ hμ hActivity E hEm hEregion)
  exact (hFubini H hMeas hKernel).1
