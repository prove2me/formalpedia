-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:18:13.903082+00:00
-- url     : https://prove2.me/submissions/30874538-c1b5-442e-8b0c-764fe0a22976

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Infinite activity makes the drift-normalised canonical Esscher renewal density blow up at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ),
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  obtain ⟨κraw, hraw, _, _, _, _, _, hrawTop⟩ :=
    bv_esscher_positive_tail_kernel_diverges_of_infinite_activity
      X hX hbv q hq φ hφ hroot hInfinite
  obtain ⟨κ, ρ, hκ, hρpos, hρone, hcont, hanti,
      hzero, hnonneg, hint, hmass⟩ :=
    bv_esscher_root_positive_subunit_kernel_package
      X hX hbv q hq φ hφ hroot
  have hdpos : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  refine ⟨κ, ρ, hκ, hρpos, hρone, hcont, hanti,
    hzero, hnonneg, hint, hmass, ?_⟩
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [(tendsto_atTop.1 hrawTop) (M * X.drift),
    self_mem_nhdsWithin] with x hx hxmem
  have hxpos : 0 < x := by simpa only [mem_Ioi] using hxmem
  have hpoint : κ x = κraw x / X.drift := by
    simp only [hκ x, hraw x, if_pos hxpos]
  rw [hpoint]
  exact (le_div_iff₀ hdpos).2 hx

