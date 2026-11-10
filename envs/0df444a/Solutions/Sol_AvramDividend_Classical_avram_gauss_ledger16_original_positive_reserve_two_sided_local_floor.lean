-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_ledger16_original_positive_reserve_two_sided_local_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:41:59.894654+00:00
-- url     : https://prove2.me/submissions/d8ab14a6-ba2c-4da8-94f9-cb2e47dfea82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_negative_postpayment_usc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Strict positivity of the actual postpayment reserve gives a positive
two-sided local floor inside a finite clock interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T t : ℝ≥0)
    (ht : t ∈ Set.Icc 0 T)
    (hPositive : 0 < x + X.X t ω - rightLimit D t ω) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ s in 𝓝[Set.Icc 0 T] t,
        δ ≤ x + X.X s ω - rightLimit D s ω := by
  let u : ℝ := x + X.X t ω - rightLimit D t ω
  have hu : 0 < u := hPositive
  refine ⟨u / 2, half_pos hu, ?_⟩
  have hUSC :=
    avram_gclose15_original_negative_postpayment_usc
      X x D hD ω T
  have hAt : UpperSemicontinuousWithinAt
      (fun s : ℝ≥0 => -(x + X.X s ω - rightLimit D s ω))
      (Set.Icc 0 T) t := hUSC t ht
  have hBelow : ∀ᶠ s in 𝓝[Set.Icc 0 T] t,
      -(x + X.X s ω - rightLimit D s ω) < -(u / 2) := by
    apply hAt
    dsimp [u]
    linarith
  filter_upwards [hBelow] with s hs
  linarith
