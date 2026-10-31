-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_trueStoppedDerivative_centredTruncatedLevy_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:42:01.839438+00:00
-- url     : https://prove2.me/submissions/a62946c5-4507-49b4-80e7-03fc58718907

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The true ruin-stopped, clipped discounted controlled-reserve derivative
is conditionally orthogonal to centred bounded Lévy increments, even if X
has no finite first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (T s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      (max (-R) (min R (X.X t ω - X.X s ω)) -
        ∫ η, max (-R) (min R (X.X (t - s) η)) ∂P))
        | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let clip : ℝ → ℝ := fun y => max (-R) (min R y)
  have hclip : Measurable clip := by
    fun_prop
  have hbound : ∀ y, ‖clip y‖ ≤ R := by
    intro y
    have hlo : -R ≤ clip y := le_max_left _ _
    have hup : clip y ≤ R :=
      max_le (by linarith) (min_le_left _ _)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hup⟩
  have hInt := avram_wave3_04_source_bounded_futurePayoff_integrable
    X (t - s) clip hclip R hbound
  let mean : ℝ := ∫ η, clip (X.X (t - s) η) ∂P
  let φ : ℝ → ℝ := fun y => clip y - mean
  have hφ : Measurable φ := hclip.sub measurable_const
  have hIntφ : Integrable (fun ω => φ (X.X (t - s) ω)) P :=
    hInt.sub (integrable_const mean)
  have hMeanZero :
      (∫ ω, φ (X.X (t - s) ω) ∂P) = 0 := by
    change (∫ ω, clip (X.X (t - s) ω) - mean ∂P) = 0
    rw [integral_sub hInt (integrable_const mean)]
    simp [mean]
  have hCE := avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
    X x D hD w q K hK T s t hst φ hφ hIntφ
  simpa only [φ, clip, mean, hMeanZero, mul_zero] using hCE
