-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux12_original_jump_laplace_finite_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:10:21.867531+00:00
-- url     : https://prove2.me/submissions/5fea80a6-b254-41fb-80d5-63b8acb15b6f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux12b_original_jump_laplace_finite_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_b20_original_all_reciprocal_jump_levels_absent_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) ≤ (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν))) := by
  intro n k
  have hNo : ∀ᵐ ω ∂P, ∀ v : ℝ≥0,
      0 < v → v ≤ (n : ℝ≥0) →
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω ≠
        (1 / ((k : ℝ) + 1)) := by
    filter_upwards
      [avram_b20_original_all_reciprocal_jump_levels_absent_ae X hX hBV]
      with ω hω
    exact hω n k
  have hSame : ∀ᵐ ω ∂P,
      (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) ≤
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0) =
      (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) <
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0) := by
    filter_upwards [hNo] with ω hn
    apply tsum_congr
    intro v
    by_cases hv : 0 < v ∧ v ≤ (n : ℝ≥0)
    · have hne := hn v hv.1 hv.2
      by_cases hlt : (1 / ((k : ℝ) + 1)) <
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      · rw [if_pos ⟨hv.1, hv.2, le_of_lt hlt⟩, if_pos ⟨hv.1, hv.2, hlt⟩]
      · have hnotle : ¬ (1 / ((k : ℝ) + 1)) ≤
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω := by
          intro hle
          exact hne (le_antisymm (le_of_not_gt hlt) hle)
        rw [if_neg (by intro h; exact hnotle h.2.2),
            if_neg (by intro h; exact hlt h.2.2)]
    · rw [if_neg (by intro h; exact hv ⟨h.1, h.2.1⟩),
          if_neg (by intro h; exact hv ⟨h.1, h.2.1⟩)]
  have hEq : (∫ ω : Ω, Real.exp (-
    ((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) ≤
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
    (∫ ω : Ω, Real.exp (-
    ((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) <
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) :=
    integral_congr_ae (hSame.mono fun ω h =>
      congrArg (fun z : ℝ≥0∞ => Real.exp (-(z.toReal))) h)
  exact hEq.trans (avram_redux12b_original_jump_laplace_finite_cutoff X hX hBV n k)
