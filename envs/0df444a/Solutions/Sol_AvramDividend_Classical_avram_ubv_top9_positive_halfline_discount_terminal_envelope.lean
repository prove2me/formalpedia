-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_positive_halfline_discount_terminal_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:41:03.420892+00:00
-- url     : https://prove2.me/submissions/125e199c-d8b6-45da-9c8d-61f2a12a7072

import Mathlib
import Theorems.Thm_AvramDividend_Classical_secant_of_derivative_lower_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*}
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_diff : DifferentiableOn ℝ w (Ioi 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (B : ℝ) (hB : 0 < B)
    (V : Ω → ℝ) (hV : ∀ ω, V ω ≤ B)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤ Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ∧
      Real.exp (-(q * (σ ω : ℝ))) * w (V ω) ≤ w B := by
  have hc : ContinuousOn w (Icc 0 B) := by
    exact hw_cont.mono (by intro y hy; exact hy.1)
  have hd : DifferentiableOn ℝ w (Ioo 0 B) := by
    exact hw_diff.mono (by intro y hy; exact hy.1)
  have hg : ∀ y ∈ Ioo (0 : ℝ) B, (1 : ℝ) ≤ deriv w y := by
    intro y hy
    exact hw_grad y hy.1
  have hs := AvramDividend.Classical.secant_of_derivative_lower_bound
    w B 1 hc hd hg
  have hwb : 0 ≤ w B := by
    have h0 := hs 0 B (le_refl (0 : ℝ)) (le_of_lt hB) (le_refl B)
    nlinarith [hw0]
  have hwbelow (y : ℝ) (hyB : y ≤ B) : 0 ≤ w y ∧ w y ≤ w B := by
    rcases lt_trichotomy y 0 with hneg | heq | hpos
    · rw [hw_neg y hneg]
      exact ⟨le_refl 0, hwb⟩
    · subst y
      have h0 := hs 0 B (le_refl (0 : ℝ)) (le_of_lt hB) (le_refl B)
      constructor
      · exact hw0
      · nlinarith
    · have hpos_bound := hs 0 y (le_refl (0 : ℝ))
        (le_of_lt hpos) hyB
      have hupper := hs y B (le_of_lt hpos) hyB (le_refl B)
      constructor <;> nlinarith [hw0]
  intro ω
  obtain ⟨hwpos, hwupper⟩ := hwbelow (V ω) (hV ω)
  have hclock : 0 ≤ (σ ω : ℝ) := NNReal.coe_nonneg _
  have hprod : 0 ≤ q * (σ ω : ℝ) := mul_nonneg hq hclock
  have hexp_nonneg : 0 ≤ Real.exp (-(q * (σ ω : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hexp_le : Real.exp (-(q * (σ ω : ℝ))) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr hprod)
  have hgap : 0 ≤ (1 - Real.exp (-(q * (σ ω : ℝ)))) * w (V ω) :=
    mul_nonneg (sub_nonneg.mpr hexp_le) hwpos
  constructor
  · exact mul_nonneg hexp_nonneg hwpos
  · nlinarith
