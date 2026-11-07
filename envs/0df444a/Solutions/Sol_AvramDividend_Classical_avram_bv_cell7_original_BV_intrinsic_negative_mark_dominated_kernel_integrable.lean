-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_negative_mark_dominated_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:11:51.616068+00:00
-- url     : https://prove2.me/submissions/0bf58ea0-eb68-4520-98c7-a2ac1b08edd0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A measurable original jump source bounded by the true negative-mark
    variation is integrable against the same intrinsic original BV measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (C : ℝ), 0 ≤ C →
      let Δ : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
            (fun u : ℝ≥0 => (u, Δ u)))
      ∀ (f : ℝ≥0 × ℝ → ℝ), Measurable f →
        (∀ p, |f p| ≤ C * max (-p.2) 0) → Integrable f NT := by
  filter_upwards
    [AvramDividend.Classical.avram_bv_cell7_original_BV_intrinsic_weighted_negative_mark_mass_finite
      X hBV] with ω hω
  intro T C hC
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
  let NT : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
        (fun u : ℝ≥0 => (u, Δ u)))
  change ∀ (f : ℝ≥0 × ℝ → ℝ), Measurable f →
    (∀ p, |f p| ≤ C * max (-p.2) 0) → Integrable f NT
  intro f hf hdom
  have hfinite : (∫⁻ p, ENNReal.ofReal (C * (-p.2)) ∂NT) < ⊤ :=
    hω T C hC
  have hpoint : ∀ p : ℝ≥0 × ℝ,
      ‖f p‖ₑ ≤ ENNReal.ofReal (C * (-p.2)) := by
    intro p
    rw [Real.enorm_eq_ofReal_abs]
    have hupper : ENNReal.ofReal |f p| ≤
        ENNReal.ofReal (C * max (-p.2) 0) :=
      ENNReal.ofReal_le_ofReal (hdom p)
    have hclip : ENNReal.ofReal (C * max (-p.2) 0) =
        ENNReal.ofReal (C * (-p.2)) := by
      by_cases hp : 0 ≤ -p.2
      · simp [max_eq_left hp]
      · have hle : -p.2 ≤ 0 := le_of_lt (lt_of_not_ge hp)
        have hprod : C * (-p.2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hle
        calc
          ENNReal.ofReal (C * max (-p.2) 0) = 0 := by
            rw [max_eq_right hle, mul_zero]
            exact ENNReal.ofReal_zero
          _ = ENNReal.ofReal (C * (-p.2)) :=
            (ENNReal.ofReal_of_nonpos hprod).symm
    exact hupper.trans_eq hclip
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  change (∫⁻ p, ‖f p‖ₑ ∂NT) < ⊤
  exact lt_of_le_of_lt (lintegral_mono hpoint) hfinite
