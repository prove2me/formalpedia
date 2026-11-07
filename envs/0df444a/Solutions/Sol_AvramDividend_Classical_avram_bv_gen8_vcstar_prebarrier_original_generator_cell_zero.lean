-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_vcstar_prebarrier_original_generator_cell_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:44:16.148946+00:00
-- url     : https://prove2.me/submissions/9877701c-dc5c-4ee9-8acc-fab8fb76ad61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section

/-- The exact pre-ruin original BV generator cell vanishes below c*. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n i : ℕ) (ω : Ω) :
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ Z < (cstar W).toReal then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) = 0 := by
  let Z : ℝ := Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z ∧ Z < (cstar W).toReal then
    Real.exp (-(q * (u n i : ℝ))) *
      (X.generator (vcstar W) Z - q * vcstar W Z) *
      ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0) = 0
  split_ifs with h
  · have hEq : X.generator (vcstar W) Z - q * vcstar W Z = 0 :=
      (generator_vcstar_eq_zero X hX q hq W hW h_smooth hc Z
        ⟨h.2.1, h.2.2⟩).2
    rw [hEq]
    ring
  · rfl
