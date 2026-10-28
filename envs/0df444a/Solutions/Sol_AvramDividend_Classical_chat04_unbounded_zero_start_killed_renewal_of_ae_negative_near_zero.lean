-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:41:39.81263+00:00
-- url     : https://prove2.me/submissions/5f4d59f5-b68d-4995-b162-3ffe2eaa87b3

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
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
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W 0) := by
  apply chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
    X hnbv q hq W hW t
  filter_upwards [hnear] with ω hω
  obtain ⟨s, hs, hsneg⟩ := hω t ht
  exact ⟨s, le_of_lt hs, hsneg⟩
