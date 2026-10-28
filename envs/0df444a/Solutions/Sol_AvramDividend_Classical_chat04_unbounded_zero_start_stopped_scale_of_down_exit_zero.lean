-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:45:34.609121+00:00
-- url     : https://prove2.me/submissions/d05397ff-57ce-4796-8f76-d64b4aa79dc9

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hdown0 : ∀ᵐ ω ∂P,
      (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) = 0) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W 0) := by
  have hW0 : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hzero : ∀ᵐ ω ∂P,
      (if (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)))))
       else 0) = 0 := by
    filter_upwards [hdown0] with ω hω
    rw [hω]
    have hn : ¬ ((⨅ (t : ℝ≥0) (_ : a < X.X t ω),
          (t : ℝ≥0∞)) < (0 : ℝ≥0∞)) := not_lt_of_ge bot_le
    simp [hn]
  have hintegral :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) = 0 := by
    calc
      _ = (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) := lintegral_congr_ae hzero
      _ = 0 := by simp
  simp [hintegral, hW0]
