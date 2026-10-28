-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:37:27.321545+00:00
-- url     : https://prove2.me/submissions/a6d421c9-53ff-4b00-b94c-0756147eada7

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Notation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (t : ℝ≥0)
    (hdown : ∀ᵐ ω ∂P, ∃ s : ℝ≥0, s ≤ t ∧ X.X s ω < 0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W 0) := by
  have hW0 : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hzero : ∀ᵐ ω ∂P,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t u))) ω = 0 := by
    filter_upwards [hdown] with ω hω
    obtain ⟨s, hs, hsneg⟩ := hω
    have hnot : ω ∉ {u : Ω | ∀ s : ℝ≥0, s ≤ t →
        0 ≤ X.X s u} := by
      intro hm
      exact (not_le_of_gt hsneg) (hm s hs)
    simp [Set.indicator, hnot]
  calc
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t ω))) ω ∂P) =
        (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) := lintegral_congr_ae hzero
    _ = ENNReal.ofReal (W 0) := by simp [hW0]
