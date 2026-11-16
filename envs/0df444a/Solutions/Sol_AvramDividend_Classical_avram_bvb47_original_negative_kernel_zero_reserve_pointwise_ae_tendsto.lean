-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb47_original_negative_kernel_zero_reserve_pointwise_ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:56:15.769647+00:00
-- url     : https://prove2.me/submissions/85739ecf-7a5f-427e-9994-c74f00d72e11

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      Tendsto
        (fun n : ℕ => w (C.toReal / ((n : ℝ) + 2) + z) -
          w (C.toReal / ((n : ℝ) + 2)))
        atTop (𝓝 (w ((0 : ℝ) + z) - w 0)) := by
  let y : ℕ → ℝ := fun n => C.toReal / ((n : ℝ) + 2)
  have hy : Tendsto y atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (tendsto_const_div_atTop_nhds_zero_nat C.toReal).comp
        (Filter.tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def, y, Nat.cast_add, Nat.cast_ofNat] using hShift
  have hyPos : ∀ n, 0 ≤ y n := by
    intro n
    dsimp [y]
    exact div_nonneg ENNReal.toReal_nonneg (by positivity)
  filter_upwards [ae_restrict_mem (measurableSet_Iio)] with z hz
  simpa only [y, zero_add] using
    (avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
      w y hy hyPos hwCont hwNeg z hz)
