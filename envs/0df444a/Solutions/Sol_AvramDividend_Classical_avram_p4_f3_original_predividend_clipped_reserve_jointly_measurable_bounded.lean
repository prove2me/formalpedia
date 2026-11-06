-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:10:27.590971+00:00
-- url     : https://prove2.me/submissions/9c6e8a56-be52-4a17-a1e5-1f34d6d9189c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original clipped pre-payment reserve is ambient measurable and bounded by K. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (δ K : ℝ) (hδK : δ ≤ K) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable U ∧ ∀ p, U p ≤ K := by
  have hY : Measurable (fun p : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) :=
    avram_integration_sweep9_original_controlled_prestate_ambient_measurable
      X x D hD
  constructor
  · exact hY.ite (hY measurableSet_Icc) measurable_const
  · intro p
    dsimp
    split_ifs with h
    · exact h.2
    · exact hδK
