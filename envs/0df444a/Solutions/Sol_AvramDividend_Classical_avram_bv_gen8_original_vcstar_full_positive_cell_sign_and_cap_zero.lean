-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:12:19.410198+00:00
-- url     : https://prove2.me/submissions/82292534-a6d0-4ab1-a90c-7ab3a92bd25f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Actual stopped BV generator cells have full HJB sign and cap zero. -/
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
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, u n i ≤ u n (i + 1)) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∀ n i ω, H n i ω ≤ 0) ∧
      ∀ n i ω,
        let Z : ℝ := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ Z ≤ (cstar W).toReal then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator (vcstar W) Z - q * vcstar W Z) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) = 0 := by
  let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change (∀ n i ω, H n i ω ≤ 0) ∧
    ∀ n i ω,
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ Z ≤ (cstar W).toReal then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) = 0
  constructor
  · intro n i ω
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0
    split_ifs with h
    · have hj := (vcstar_hjb_all_positive_of_generator
          X hX q hq W hW hc (Or.inr (Or.inl hBV)) hgen Z h.2).2
      have hG : X.generator (vcstar W) Z - q * vcstar W Z ≤ 0 := by
        calc
          X.generator (vcstar W) Z - q * vcstar W Z ≤
              max (X.generator (vcstar W) Z - q * vcstar W Z)
                (1 - deriv (vcstar W) Z) := le_max_left _ _
          _ = 0 := hj
      have hwidth : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
        exact sub_nonneg.mpr (by exact_mod_cast hmono n i)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hG)
        hwidth
    · exact le_refl 0
  · intro n i ω
    exact avram_bv_gen8_vcstar_closed_prebarrier_original_generator_cell_zero
      X hX hBV q hq W hW hc hcpos hgen x D u n i ω
