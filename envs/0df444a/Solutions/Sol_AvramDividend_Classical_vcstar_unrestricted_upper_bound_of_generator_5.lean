-- Prove2me | solution 5 for AvramDividend.Classical.vcstar_unrestricted_upper_bound_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:40:17.528654+00:00
-- url     : https://prove2.me/submissions/346459fe-e4bc-4a28-9689-ae3df86cc25f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_truncated_hjb_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x) := by
  obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
    vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
  have hsubset :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hsmoothTop :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)}) :=
    ⟨fun h => (hsmooth.1 h).mono hsubset,
     fun h => (hsmooth.2 h).mono hsubset⟩
  have hhjbTop :
      ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (⊤ : ℝ≥0∞) →
        X.GeneratorIntegrable (vcstar W) y ∧
          max (X.generator (vcstar W) y - q * vcstar W y)
              (1 - deriv (vcstar W) y) = 0 := by
    intro y hy _
    exact vcstar_hjb_all_positive_of_generator
      X hX q hq W hW hc h_smooth hgen y hy
  have hBudget :
      ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ (⊤ : ℝ≥0∞) →
        ∀ D : ℝ≥0 → Ω → ℝ,
          IsAdmissibleLe X x (⊤ : ℝ≥0∞) D →
            ∀ n : ℕ,
              (∫⁻ ω, ∫⁻ t in
                paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω) ∂P) ≤
                ENNReal.ofReal (vcstar W x) := by
    intro x hx hxC D hD n
    exact admissible_cap_truncated_dividendValue_le
      X hX q hq (vcstar W) (⊤ : ℝ≥0∞) ENNReal.zero_lt_top
      hcont hw0 hwneg hsmoothTop hhjbTop x hx hxC D hD
      (n : ℝ) (by positivity)
  exact (local_verification_from_uniform_truncated_hjb_budget
    X q (vcstar W) (⊤ : ℝ≥0∞) hBudget).2 rfl
