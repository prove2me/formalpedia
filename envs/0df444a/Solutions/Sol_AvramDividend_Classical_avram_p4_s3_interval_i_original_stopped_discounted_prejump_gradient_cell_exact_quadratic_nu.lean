-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_stopped_discounted_prejump_gradient_cell_exact_quadratic_nu
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:37:07.425421+00:00
-- url     : https://prove2.me/submissions/cb7fe204-273d-431b-8c4c-bf9ed639cbfd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- True stopped original controlled pre-jump derivative: exact intrinsic full
negative-cutoff physical cell ν-isometry and zero mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (s T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : Ω → ℝ := fun ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0) then 0
      else max (-K) (min K (Real.exp (-(q * (s : ℝ))) *
        deriv w (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) s)))
    let Z : Ω → ℝ := fun ω => H ω * ((N ω).toReal - r)
    MemLp Z 2 P ∧
    (∫ ω, (Z ω) ^ 2 ∂P) = r * (∫ ω, (H ω) ^ 2 ∂P) ∧
    (∫ ω, Z ω ∂P) = 0 := by
  classical
  let R : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(q * (t : ℝ))) * deriv w (R t ω)
  have hR : IsStronglyPredictable 𝓕.rightCont R := by
    simpa only [R] using
      (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD)
  have hG : IsStronglyPredictable 𝓕.rightCont G := by
    simpa only [G] using
      (avram_wave3_04_discounted_deriv_stronglyPredictable R hR w q)
  have hClip :=
    avram_wave3_04_clipped_stronglyPredictable_bounded G hG K hK
  let H : Ω → ℝ := fun ω =>
    if (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0) then 0
    else max (-K) (min K (G s ω))
  have hS : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} :=
    hτstop s
  have hH : StronglyMeasurable[𝓕.rightCont s] H := by
    exact StronglyMeasurable.ite hS stronglyMeasurable_const
      (hClip.1.stronglyAdapted s)
  have hBound (ω : Ω) : |H ω| ≤ K := by
    by_cases hs : (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
    · simpa only [H, if_pos hs, abs_zero] using hK
    · simpa only [H, if_neg hs, Real.norm_eq_abs] using hClip.2 s ω
  have hIso :=
    avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
      X s T cut H hH K hBound
  have hMart :=
    avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
      X s T cut H hH K hBound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [R, G, H] using hIso.1
  · simpa only [R, G, H] using hIso.2
  · simpa only [R, G, H] using hMart.2.2
