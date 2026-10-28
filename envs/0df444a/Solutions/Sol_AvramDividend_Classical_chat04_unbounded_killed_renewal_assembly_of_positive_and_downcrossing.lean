-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_renewal_assembly_of_positive_and_downcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:49:23.651924+00:00
-- url     : https://prove2.me/submissions/b83a4297-ae1e-430f-89e8-d248aa5fee34

import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_renewal_zero_horizon_or_negative_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Assemble the full unbounded-variation killed q-scale identity from the
    positive-reserve case and instantaneous downward passage at the origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hpositive : ∀ (x : ℝ) (hx : 0 < x) (t : ℝ≥0) (ht : 0 < t),
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
        ENNReal.ofReal (W x))
    (hdown : ∀ (t : ℝ≥0), 0 < t →
      ∀ᵐ ω ∂P, ∃ s : ℝ≥0, s ≤ t ∧ X.X s ω < 0)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by
  by_cases ht : t = 0
  · exact chat04_history_killed_renewal_zero_horizon_or_negative_reserve
      X q W hW x t (Or.inl ht)
  by_cases hxneg : x < 0
  · exact chat04_history_killed_renewal_zero_horizon_or_negative_reserve
      X q W hW x t (Or.inr hxneg)
  have htpos : 0 < t :=
    lt_of_le_of_ne (bot_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht)
  by_cases hxzero : x = 0
  · subst x
    simpa only [zero_add] using
      chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing
        X hnbv q hq W hW t (hdown t htpos)
  have hxle : 0 ≤ x := le_of_not_gt hxneg
  have hxpos : 0 < x := lt_of_le_of_ne hxle (Ne.symm hxzero)
  exact hpositive x hxpos t htpos
