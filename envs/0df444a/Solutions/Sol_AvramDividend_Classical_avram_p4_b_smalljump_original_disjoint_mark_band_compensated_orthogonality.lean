-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:57.322794+00:00
-- url     : https://prove2.me/submissions/0b843775-a374-434f-a205-10585937db8d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Two distinct original intrinsic marked-band counts have orthogonal
centred increments when their physical cross factorial moment factors. -/
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
    (hJA : Integrable JA P) (hJB : Integrable JB P)
    (hCrossInt : Integrable (fun ω => JA ω * JB ω) P)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirstA : (∫ ω, JA ω ∂P) = rA)
    (hFirstB : (∫ ω, JB ω ∂P) = rB)
    (hCross : (∫ ω, JA ω * JB ω ∂P) = rA * rB) :
    (∫ ω, (JA ω - rA) * (JB ω - rB) ∂P) = 0 := by
  have hLinA : Integrable (fun ω => rB * JA ω) P :=
    hJA.const_mul _
  have hLinB : Integrable (fun ω => rA * JB ω) P :=
    hJB.const_mul _
  have hConst : Integrable (fun _ : Ω => rA * rB) P :=
    integrable_const _
  have hPoint (ω : Ω) :
      (JA ω - rA) * (JB ω - rB) =
      (JA ω * JB ω - rB * JA ω - rA * JB ω) + rA * rB := by
    ring
  have hAdd :
      (∫ ω, (JA ω * JB ω - rB * JA ω - rA * JB ω) + rA * rB ∂P) =
      (∫ ω, JA ω * JB ω - rB * JA ω - rA * JB ω ∂P) +
        (∫ _ : Ω, rA * rB ∂P) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      (integral_add ((hCrossInt.sub hLinA).sub hLinB) hConst)
  have hSubB :
      (∫ ω, JA ω * JB ω - rB * JA ω - rA * JB ω ∂P) =
      (∫ ω, JA ω * JB ω - rB * JA ω ∂P) -
        (∫ ω, rA * JB ω ∂P) := by
    simpa only [Pi.sub_apply] using
      (integral_sub (hCrossInt.sub hLinA) hLinB)
  have hSubA :
      (∫ ω, JA ω * JB ω - rB * JA ω ∂P) =
      (∫ ω, JA ω * JB ω ∂P) -
        (∫ ω, rB * JA ω ∂P) := by
    simpa only [Pi.sub_apply] using
      (integral_sub hCrossInt hLinA)
  calc
    _ = (∫ ω, (JA ω * JB ω - rB * JA ω - rA * JB ω) + rA * rB ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hPoint ω
    _ = (∫ ω, JA ω * JB ω - rB * JA ω - rA * JB ω ∂P) +
        (∫ _ : Ω, rA * rB ∂P) := hAdd
    _ = ((∫ ω, JA ω * JB ω ∂P) -
        (∫ ω, rB * JA ω ∂P) -
        (∫ ω, rA * JB ω ∂P)) + rA * rB := by
      rw [hSubB, hSubA]
      simp
    _ = 0 := by
      rw [integral_const_mul, integral_const_mul,
        hFirstA, hFirstB, hCross]
      ring
