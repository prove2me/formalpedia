-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:29:13.564297+00:00
-- url     : https://prove2.me/submissions/79160ffc-601c-4d80-abfa-db4ccef5005f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original BV physical negative first moment makes every bounded
predictable interior C1 discounted small-source-mark kernel truly integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (hMeas : AEStronglyMeasurable (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (X.ν.restrict (Ioo (-a / 2) 0))) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (Ioo (-a / 2) 0) X.ν := by
  have hSub : Ioo (-a / 2) (0 : ℝ) ⊆ Ioo (-1) 0 := by
    intro z hz
    exact ⟨by linarith [hz.1, ha2], hz.2⟩
  have hFirst : IntegrableOn (fun z : ℝ => -z)
      (Ioo (-a / 2) 0) X.ν :=
    (bv_small_negative_first_moment_integrable X hBV).mono_set hSub
  have hMajor : IntegrableOn (fun z : ℝ => L * (-z))
      (Ioo (-a / 2) 0) X.ν := hFirst.const_mul L
  apply hMajor.mono' hMeas
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
  have hsmall : -a / 2 ≤ z ∧ z ≤ 0 :=
    ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hBound :=
    avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
      X x D w q hq a b L ha hab hL hLip ω t hBand z hsmall
  have hPos : 0 ≤ L * (-z) := mul_nonneg hL (neg_nonneg.mpr hsmall.2)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hPos,
    abs_of_neg hz.2] using hBound
