-- Prove2me | solution 2 for AvramDividend.Classical.local_verification_separated_countable_dividend_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:06:31.46556+00:00
-- url     : https://prove2.me/submissions/83d7689a-4b32-4073-bdbc-82ce29b92cfc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividendMeasure_bound_separated
import Theorems.Thm_AvramDividend_Classical_local_verification_separated_countable_jump_drop_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w x)  := by
  exact le_trans
    (AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated
      X x q w C hw_cont hw_smooth hw_gen hw_grad D hD hxC
      ω S hCountable hNonneg hActive)
    (AvramDividend.Classical.local_verification_separated_countable_jump_drop_budget
      X x q w C hw_cont hw_smooth hw_gen hw_grad D hD hxC
      ω S hCountable hNonneg hActive)
