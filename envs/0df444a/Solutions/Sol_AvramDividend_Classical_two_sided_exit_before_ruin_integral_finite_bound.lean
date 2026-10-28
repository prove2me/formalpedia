-- Prove2me | solution 1 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_finite_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:35:07.704547+00:00
-- url     : https://prove2.me/submissions/445e0ad6-1c5f-463c-84ec-55e86726a658

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤ 1 := by
  haveI := X.isProbability
  have hexp_bound : ∀ ω : Ω,
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞))))) ≤ 1 := by
    intro ω
    rw [ENNReal.ofReal_le_one]
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hq.le ENNReal.toReal_nonneg)
  have hbound : ∀ ω : Ω,
      (if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0) ≤ 1 := by
    intro ω
    by_cases h : (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞))
    · rw [if_pos h]
      exact hexp_bound ω
    · rw [if_neg h]
      exact bot_le
  calc (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P)
      ≤ ∫⁻ _ : Ω, 1 ∂P :=
        MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall hbound)
    _ = 1 := by simp
