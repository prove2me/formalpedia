-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_tail_real_conversion_of_finite_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:58:57.927474+00:00
-- url     : https://prove2.me/submissions/8748afbd-34c1-4d96-bdea-08c398535d8a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_kernel_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ)
    (hTailFin : ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤)
    (θ : ℝ) (hθ : 0 < θ)
    (L : ℝ≥0∞) (hLfinite : L ≠ ⊤)
    (hTon : (∫⁻ t in Ioi (0 : ℝ),
        ν (Iio (-t)) * ENNReal.ofReal (1 - Real.exp (-θ * t))) = L) :
    IntegrableOn (fun t : ℝ =>
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal)
      (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) =
      L.toReal := by
  have hMono : Antitone (fun t : ℝ => ν (Iio (-t))) := by
    intro a b hab
    apply measure_mono
    intro y hy
    exact lt_of_lt_of_le hy (neg_le_neg hab)
  have hMeas : Measurable (fun t : ℝ =>
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) :=
    (by fun_prop : Measurable
      (fun t : ℝ => 1 - Real.exp (-θ * t))).mul
        hMono.measurable.ennreal_toReal
  have hAE : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)]
      (fun t : ℝ => (1 - Real.exp (-θ * t)) *
        (ν (Iio (-t))).toReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt (by simpa only [mem_Ioi] using ht)
    exact mul_nonneg
      (levy_compensated_exponential_kernel_bounds θ t hθ.le ht0).1
      ENNReal.toReal_nonneg
  have hlin : (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (-θ * t)) *
          (ν (Iio (-t))).toReal)) = L := by
    rw [← hTon]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := by simpa only [mem_Ioi] using ht
    dsimp only
    rw [ENNReal.ofReal_mul
      (levy_compensated_exponential_kernel_bounds θ t hθ.le htpos.le).1]
    rw [ENNReal.ofReal_toReal (ne_of_lt (hTailFin t htpos))]
    exact mul_comm _ _
  have hInt : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-θ * t)) *
        (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable
      hMeas.aestronglyMeasurable hAE).mp (by rw [hlin]; exact hLfinite)
  have hReal := ofReal_integral_eq_lintegral_ofReal hInt hAE
  refine ⟨hInt, ?_⟩
  calc
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) =
        (ENNReal.ofReal (∫ t in Ioi (0 : ℝ),
          (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal)).toReal :=
            (ENNReal.toReal_ofReal (integral_nonneg_of_ae hAE)).symm
    _ = L.toReal := by rw [hReal, hlin]
