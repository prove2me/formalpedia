-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_signed_jump_pos_neg_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:31:22.406895+00:00
-- url     : https://prove2.me/submissions/a3ea1cca-f882-4971-9cb2-be32bb295c8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_source_nonlinear_jump_count_eq_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Both signed parts of the original marked jump source are counted
exactly over a measurable stopped set of physical times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    [DecidablePred (fun u : ℝ≥0 => u ∈ S)]
    (F : ℝ≥0 × ℝ → ℝ) (hF : Measurable F) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ((∫⁻ p, (if p.1 ∈ S then ENNReal.ofReal (F p) else 0) ∂NX) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
            ∧ u ∈ S then
          ENNReal.ofReal (F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) ∧
    ((∫⁻ p, (if p.1 ∈ S then ENNReal.ofReal (-F p) else 0) ∂NX) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
            ∧ u ∈ S then
          ENNReal.ofReal (-F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        else 0) := by
  dsimp
  have hPos : Measurable
      (fun p : ℝ≥0 × ℝ => if p.1 ∈ S then ENNReal.ofReal (F p) else 0) :=
    Measurable.ite (hS.preimage measurable_fst)
      (ENNReal.measurable_ofReal.comp hF) measurable_const
  have hNeg : Measurable
      (fun p : ℝ≥0 × ℝ => if p.1 ∈ S then ENNReal.ofReal (-F p) else 0) :=
    Measurable.ite (hS.preimage measurable_fst)
      (ENNReal.measurable_ofReal.comp hF.neg) measurable_const
  constructor
  · calc
      _ = ∑' u : ℝ≥0, if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
          (if u ∈ S then ENNReal.ofReal (F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0)
          else 0 :=
        avram_p3_2_original_source_nonlinear_jump_count_eq_tsum X ω _ hPos
      _ = _ := by
        apply tsum_congr
        intro u
        by_cases hj : 0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
        · simp [hj]
        · simp [hj]
  · calc
      _ = ∑' u : ℝ≥0, if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
          (if u ∈ S then ENNReal.ofReal (-F (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0)
          else 0 :=
        avram_p3_2_original_source_nonlinear_jump_count_eq_tsum X ω _ hNeg
      _ = _ := by
        apply tsum_congr
        intro u
        by_cases hj : 0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
        · simp [hj]
        · simp [hj]
