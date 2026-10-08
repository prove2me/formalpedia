-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_esscher_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:11:34.08701+00:00
-- url     : https://prove2.me/submissions/55062493-ebe4-404a-b2c4-57e83fecd55b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_shifted_kernel_gap_on_halfline_canonical
import Theorems.Thm_AvramDividend_Classical_bv_geometric_factor_scale_denominator
import Theorems.Thm_AvramDividend_Classical_positive_continuous_root_from_growth
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  have hδ : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  let a : ℝ := q / X.drift
  have ha : 0 < a := div_pos hq hδ
  obtain ⟨b, hb, hgap⟩ :=
    bv_shifted_kernel_gap_on_halfline_canonical X hX q hq hbv
  let s : ℝ := max b (1 - a) + 1
  have hbs : b ≤ s := by
    dsimp [s]
    linarith [le_max_left b (1 - a)]
  have hs : 0 < s := by
    dsimp [s]
    linarith [le_max_left b (1 - a)]
  have hθ : 1 ≤ s + q / X.drift := by
    change 1 ≤ s + a
    dsimp [s]
    linarith [le_max_right b (1 - a)]
  have hψ : q < X.ψ (s + q / X.drift) :=
    (bv_geometric_factor_scale_denominator X hX q hq hbv s hs hθ
      (hgap s hbs)).1
  have hA : 0 < s + q / X.drift := by
    change 0 < s + a
    linarith
  obtain ⟨φ, hφ, _, hroot⟩ :=
    positive_continuous_root_from_growth (X.ψ)
      q (s + q / X.drift) hq hA
      (levy_laplace_exponent_continuousOn_nonnegative X)
      (levy_laplace_exponent_zero X) hψ
  exact ⟨φ, hφ, hroot⟩
