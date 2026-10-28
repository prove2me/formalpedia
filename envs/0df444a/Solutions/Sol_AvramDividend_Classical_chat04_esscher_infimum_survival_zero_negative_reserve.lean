-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_infimum_survival_zero_negative_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:14:55.171995+00:00
-- url     : https://prove2.me/submissions/84a02693-54b9-42b9-9bb5-02834348a56f

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat01_negative_initial_reserve_survival_empty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (hx : x < 0) :
    (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) = 0 := by
  have hzero : ∀ t : ℝ≥0,
      (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) = 0 := by
    intro t
    rw [chat01_negative_initial_reserve_survival_empty X x hx t]
    simp
  simp only [hzero, ENNReal.ofReal_zero, iInf_const]
