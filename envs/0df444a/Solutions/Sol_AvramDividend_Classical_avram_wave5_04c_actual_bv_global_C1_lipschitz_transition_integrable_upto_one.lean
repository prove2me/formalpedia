-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:56:02.320196+00:00
-- url     : https://prove2.me/submissions/f14691d7-5bae-4b8e-ac1f-3bc6000f7ffa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_source_X_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    Integrable (fun ω => w (x + X.X t ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hXt : Integrable (X.X t) P :=
    avram_wave5_04c_actual_bv_source_X_integrable_upto_one X hX hBV t ht
  have hG : Integrable
      (fun ω : Ω => |w x| + L * |X.X t ω|) P := by
    exact (integrable_const (|w x|)).add (hXt.abs.const_mul L)
  have hwmeas : Measurable w := hwC1.continuous.measurable
  have hXmeas : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le _) le_rfl
  have hmeas : Measurable (fun ω => w (x + X.X t ω)) :=
    hwmeas.comp (measurable_const.add hXmeas)
  have hb : ∀ᵐ ω ∂P,
      ‖w (x + X.X t ω)‖ ≤ |w x| + L * |X.X t ω| := by
    filter_upwards [] with ω
    have hlip : |w (x + X.X t ω) - w x| ≤ L * |X.X t ω| := by
      simpa only [add_sub_cancel_left] using hLip (x + X.X t ω) x
    calc
      ‖w (x + X.X t ω)‖ = |w (x + X.X t ω)| := Real.norm_eq_abs _
      _ = |(w (x + X.X t ω) - w x) + w x| := by congr 1; ring
      _ ≤ |w (x + X.X t ω) - w x| + |w x| := abs_add_le _ _
      _ ≤ L * |X.X t ω| + |w x| := add_le_add_left hlip _
      _ = |w x| + L * |X.X t ω| := by ring
  exact hG.mono' hmeas.aestronglyMeasurable hb