-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f5_original_postpayment_zero_cap_or_strict_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:24:54.874+00:00
-- url     : https://prove2.me/submissions/b208d902-1a2b-4564-aab7-c28bd598b4bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original postpayment reserve is either at a boundary or lies in the
strict C2 interior where both HJB signs are available. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω)) :
    let y := x + X.X t ω - rightLimit D t ω
    y = 0 ∨ ENNReal.ofReal y = C ∨
      (0 < y ∧ ENNReal.ofReal y < C ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧
        1 ≤ deriv w y) := by
  dsimp
  rcases avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
      X x C D hD hxc ω t ht with hzero | hcap | ⟨hy, hycap⟩
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hcap)
  · obtain ⟨hGI, hG⟩ := hw_gen _ hy hycap
    exact Or.inr (Or.inr ⟨hy, hycap, hGI, hG, hw_grad _ hy hycap⟩)
