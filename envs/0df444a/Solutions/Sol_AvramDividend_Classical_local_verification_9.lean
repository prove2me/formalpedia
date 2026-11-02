-- Prove2me | solution 9 for AvramDividend.Classical.local_verification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:19:06.861201+00:00
-- url     : https://prove2.me/submissions/43eb93ab-6ef9-4186-8ffd-ee56e974c361
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_truncated_hjb_budget
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core_positive_cap
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_core_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-- Assemble Proposition 4(i) from source-faithful BV and corrected UBV
stochastic cores, preserving the original dividend process and HJB hypotheses.
The two stochastic cores remain explicit Open dependencies until proved. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  apply local_verification_from_uniform_truncated_hjb_budget X q w C
  intro x hx hxc D hD n
  obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
    local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hw_smooth hw_hjb x hxc D hD
  by_cases hBV : X.BoundedVariation
  · exact admissible_cap_truncated_bv_stochastic_core_positive_cap
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      (hw_smooth.2 hBV) hgen hgrad x hx hxc D hD
      hnonneg hjump (n : ℝ) (Nat.cast_nonneg n)
  · exact admissible_cap_truncated_ubv_stochastic_core_corrected
      X hX hBV q hq w C hw0 hw_cont hw_neg
      (hw_smooth.1 hBV) hgen hgrad x hxc D hD
      hnonneg hjump (n : ℝ) (Nat.cast_nonneg n)
