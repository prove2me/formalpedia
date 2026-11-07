-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:39:45.770003+00:00
-- url     : https://prove2.me/submissions/7cb58427-944d-4f1e-8875-f90231082a71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original positive stopped vcstar generator is supported strictly above cstar. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n i : ℕ) (ω : Ω) :
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) =
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          (cstar W).toReal < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) := by
  let Z : ℝ := Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let A : ℝ := Real.exp (-(q * (u n i : ℝ))) *
    (X.generator (vcstar W) Z - q * vcstar W Z) *
    ((u n (i + 1) : ℝ) - (u n i : ℝ))
  change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z
    then A else 0) =
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      (cstar W).toReal < Z then A else 0)
  by_cases hActive : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z
  · by_cases hAbove : (cstar W).toReal < Z
    · simp [hActive, hActive.1, hAbove]
    · have hLe : Z ≤ (cstar W).toReal := le_of_not_gt hAbove
      have hCap := avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
        X hX hBV q hq W hW hc hcpos hgen x D u n i ω
      have hZero : A = 0 := by
        change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ Z ≤ (cstar W).toReal then A else 0) = 0 at hCap
        simpa [hActive, hLe] using hCap
      simp [hActive, hAbove, hZero]
  · have hNotAbove : ¬((u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      (cstar W).toReal < Z) := by
      intro h
      apply hActive
      exact ⟨h.1, lt_of_le_of_lt (by positivity : 0 ≤ (cstar W).toReal) h.2⟩
    simp [hActive, hNotAbove]
