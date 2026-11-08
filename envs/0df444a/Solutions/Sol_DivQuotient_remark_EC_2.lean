-- Prove2me | solution 1 for DivQuotient.remark_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:34:40.150418+00:00
-- url     : https://prove2.me/submissions/c932a8ba-7b0b-4b5b-b9e0-925f0f521eae

import Mathlib
import Definitions.Def_DivQuotient_RiskMeasure

open MeasureTheory

open DivQuotient in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (φ : Lp ℝ ⊤ P → ℝ) (hφ : DivQuotient.IsSublinear φ) (hnl : ¬ DivQuotient.IsLinear φ) :
    ∃ Y : Lp ℝ ⊤ P, 0 < φ Y + φ (-Y) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hsub, hhom⟩ := hφ
  have h0 : φ 0 = 0 := by
    have := hhom 2 0 (by norm_num)
    rw [smul_zero] at this
    linarith
  have hodd : ∀ Y, φ (-Y) = -φ Y := by
    intro Y
    have h1 := hcon Y
    have h2 := hsub Y (-Y)
    rw [add_neg_cancel, h0] at h2
    linarith
  have hadd : ∀ X Y, φ (X + Y) = φ X + φ Y := by
    intro X Y
    have h1 := hsub X Y
    have h2 := hsub (-X) (-Y)
    rw [← neg_add, hodd, hodd, hodd] at h2
    linarith
  have hsm : ∀ (a : ℝ) X, φ (a • X) = a * φ X := by
    intro a X
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have := hhom (-a) X (by linarith)
      rw [neg_smul, hodd] at this
      linarith
    · subst ha
      rw [zero_smul, h0, zero_mul]
    · exact hhom a X ha
  apply hnl
  intro X Y a b
  rw [hadd, hsm, hsm]
