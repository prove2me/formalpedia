-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:05:01.458121+00:00
-- url     : https://prove2.me/submissions/320761ba-2512-4686-b885-0575064e4dce

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original stopped BV generator contribution also vanishes at the cap. -/
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
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ Z ≤ (cstar W).toReal then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) = 0 := by
  let Z : ℝ := Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z ∧ Z ≤ (cstar W).toReal then
    Real.exp (-(q * (u n i : ℝ))) *
      (X.generator (vcstar W) Z - q * vcstar W Z) *
      ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) = 0
  split_ifs with h
  · have hEq : X.generator (vcstar W) Z - q * vcstar W Z = 0 := by
      rcases lt_or_eq_of_le h.2.2 with hlt | heq
      · exact (generator_vcstar_eq_zero X hX q hq W hW
          (Or.inr (Or.inl hBV)) hcpos Z ⟨h.2.1, hlt⟩).2
      · rw [heq]
        exact (vcstar_generator_eq_zero_at_positive_cstar X hX q hq W hW hc
          hcpos (Or.inr (Or.inl hBV)) hgen).2
    rw [hEq]
    ring
  · rfl
