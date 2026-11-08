-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_vcstar_generator_interior_cell_L1_any_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:45:51.201971+00:00
-- url     : https://prove2.me/submissions/085e9793-4eb6-4bc4-acae-ace5337a6000

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped physical BV generator cell, at interior cstar, is identically zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0) :
    ∀ n i,
      let H : Ω → ℝ := fun ω =>
        let Z : ℝ := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z ∧ ENNReal.ofReal Z < cstar W then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator (vcstar W) Z - q * vcstar W Z) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
      (∀ ω, H ω = 0) ∧ Integrable H P := by
  intro n i
  let H : Ω → ℝ := fun ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ ENNReal.ofReal Z < cstar W then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change (∀ ω, H ω = 0) ∧ Integrable H P
  have hzero : ∀ ω, H ω = 0 := by
    intro ω
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ ENNReal.ofReal Z < cstar W then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) = 0
    by_cases ha : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z ∧ ENNReal.ofReal Z < cstar W
    · have hle : Z ≤ (cstar W).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hc)).mp (le_of_lt ha.2.2)
      have hg : X.generator (vcstar W) Z - q * vcstar W Z = 0 := by
        by_cases hlt : Z < (cstar W).toReal
        · exact (generator_vcstar_eq_zero_bv_unconditional_20261026
            X hX hBV q hq W hW hcpos Z ⟨ha.2.1, hlt⟩).2
        · have heq : Z = (cstar W).toReal :=
            le_antisymm hle (le_of_not_gt hlt)
          rw [heq]
          exact (avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
            X hX q hq W hW hc hcpos (Or.inr (Or.inl hBV))).2
      rw [if_pos ha, hg]
      ring
    · simp only [if_neg ha]
  refine ⟨hzero, ?_⟩
  have heq : H = (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    exact hzero ω
  rw [heq]
  exact integrable_zero Ω ℝ P
