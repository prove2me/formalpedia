-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_sourceClippedDiscountedDerivative_centredCell_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:22:01.805591+00:00
-- url     : https://prove2.me/submissions/64e50205-47db-42a6-8926-d770e566b3ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The clipped discounted derivative of the genuine controlled reserve
pre-jump state is a zero-mean finite-grid Lévy stochastic coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    (∫ ω,
      max (-K) (min K
        (Real.exp (-(q * (s : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s))) *
      φ (X.X t ω - X.X s ω) ∂P) = 0 := by
  have hR :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    Real.exp (-(q * (u : ℝ))) *
      deriv w (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)
  have hZ : IsStronglyPredictable 𝓕.rightCont Z :=
    avram_wave3_04_discounted_deriv_stronglyPredictable
      (fun u ω => Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)
      hR w q
  have hClip := avram_wave3_04_clipped_stronglyPredictable_bounded
    Z hZ K hK
  have hH : StronglyMeasurable[𝓕.rightCont s]
      (fun ω => max (-K) (min K (Z s ω))) :=
    hClip.1.stronglyAdapted s
  obtain ⟨Y, hYX, _, _, _⟩ := levy_rightCont_process X
  have hIntY : Integrable
      (fun ω => φ (Y.X (t - s) ω)) P := by
    simpa only [hYX] using hInt
  have hmeanY :
      (∫ ω, φ (Y.X (t - s) ω) ∂P) = 0 := by
    simpa only [hYX] using hmean
  have hEq := avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
    Y s t hst φ hφ
    (fun ω => max (-K) (min K (Z s ω)))
    hH K (hClip.2 s) hIntY hmeanY
  simpa only [hYX] using hEq
