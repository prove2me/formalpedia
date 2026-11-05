-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_two_disjoint_band_compensated_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:38:31.665801+00:00
-- url     : https://prove2.me/submissions/24a5f96f-5572-448c-87fb-7b54969b7c93

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original physical L² budget for two finite Lévy mark cells, from
their diagonal variances and compensated cross-band orthogonality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (A B : Set ℝ) (hDisjoint : Disjoint A B)
    (JA JB : Ω → ℝ)
    (hSourceA : ∀ ω, JA ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ A)).toReal)
    (hSourceB : ∀ ω, JB ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hIA : Integrable (fun ω => (JA ω - rA) ^ 2) P)
    (hIB : Integrable (fun ω => (JB ω - rB) ^ 2) P)
    (hICross : Integrable (fun ω =>
      (JA ω - rA) * (JB ω - rB)) P)
    (hVarA : (∫ ω, (JA ω - rA) ^ 2 ∂P) = rA)
    (hVarB : (∫ ω, (JB ω - rB) ^ 2 ∂P) = rB)
    (hOrth : (∫ ω,
      (JA ω - rA) * (JB ω - rB) ∂P) = 0)
    (cA cB : ℝ) :
    (∫ ω, (cA * (JA ω - rA) + cB * (JB ω - rB)) ^ 2 ∂P) =
      cA ^ 2 * rA + cB ^ 2 * rB := by
  have hI1 : Integrable (fun ω => cA ^ 2 * (JA ω - rA) ^ 2) P :=
    hIA.const_mul _
  have hI2 : Integrable (fun ω => cB ^ 2 * (JB ω - rB) ^ 2) P :=
    hIB.const_mul _
  have hI3 : Integrable (fun ω =>
      (2 * cA * cB) * ((JA ω - rA) * (JB ω - rB))) P :=
    hICross.const_mul _
  calc
    _ = (∫ ω, (cA ^ 2 * (JA ω - rA) ^ 2 +
      cB ^ 2 * (JB ω - rB) ^ 2) +
      (2 * cA * cB) * ((JA ω - rA) * (JB ω - rB)) ∂P) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
    _ = cA ^ 2 * rA + cB ^ 2 * rB := by
      calc
        _ = (∫ ω, cA ^ 2 * (JA ω - rA) ^ 2 +
          cB ^ 2 * (JB ω - rB) ^ 2 ∂P) +
          (∫ ω, (2 * cA * cB) *
            ((JA ω - rA) * (JB ω - rB)) ∂P) := by
              simpa only [Pi.add_apply] using integral_add (hI1.add hI2) hI3
        _ = (∫ ω, cA ^ 2 * (JA ω - rA) ^ 2 ∂P) +
          (∫ ω, cB ^ 2 * (JB ω - rB) ^ 2 ∂P) +
          (∫ ω, (2 * cA * cB) *
            ((JA ω - rA) * (JB ω - rB)) ∂P) := by
              rw [show (∫ ω, cA ^ 2 * (JA ω - rA) ^ 2 +
                cB ^ 2 * (JB ω - rB) ^ 2 ∂P) =
                (∫ ω, cA ^ 2 * (JA ω - rA) ^ 2 ∂P) +
                (∫ ω, cB ^ 2 * (JB ω - rB) ^ 2 ∂P) from by
                  simpa only [Pi.add_apply] using integral_add hI1 hI2]
        _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul,
            hVarA, hVarB, hOrth]
          ring
