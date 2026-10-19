-- Prove2me | solution 1 for CohnElkies.exists_lowerGammaScaledPositivePart_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/fa3c63f3-d403-45b1-a7f1-c58a0a5ce59a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_nonneg
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_integral_le
import Theorems.Thm_CohnElkies_lowerGammaScaledPositivePart_support

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 2 ≤ d →
        Function.support (lowerGammaScaledPositivePart d c) ⊆
            Icc (-C) C ∧
          (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
            C * ((d : ℝ) / 2) := by
  let J : ℝ :=
    ∫ Y : ℝ, max (Real.log
      (4 * Real.pi * c ^ 2 / |Y|)) 0
  let K : ℝ :=
    ∫ Y : ℝ, Real.log (lowerCoth (Real.pi * |Y| / 2))
  let B : ℝ := max 1 (8 * Real.pi * c ^ 2)
  let C : ℝ := max B (J + (1 / 2 : ℝ) * K)
  have hB : 1 ≤ B := le_max_left 1 _
  have hC : B ≤ C := le_max_left _ _
  have hK : 0 ≤ K := by
    try dsimp [K]
    apply integral_nonneg
    intro Y
    by_cases hY : Y = 0
    · simp [hY, lowerCoth]
    · exact lowerCoth_log_nonneg (by positivity)
  refine ⟨C, by linarith, ?_⟩
  intro d hd
  constructor
  · intro Y hY
    have hsupport :=
      lowerGammaScaledPositivePart_support hd hc hY
    exact ⟨le_trans (neg_le_neg hC) hsupport.1,
      le_trans hsupport.2 hC⟩
  · have hℓ : 1 ≤ (d : ℝ) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      exact_mod_cast hd
    have hmain := lowerGammaScaledPositivePart_integral_le hd hc
    change
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        ((d : ℝ) / 2) * J + (1 / 2 : ℝ) * K at hmain
    have hphase :
        ((d : ℝ) / 2) * J + (1 / 2 : ℝ) * K ≤
          ((d : ℝ) / 2) *
            (J + (1 / 2 : ℝ) * K) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hℓ) hK]
    have hconstant : J + (1 / 2 : ℝ) * K ≤ C :=
      le_max_right B _
    calc
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        ((d : ℝ) / 2) * J + (1 / 2 : ℝ) * K := hmain
      _ ≤ ((d : ℝ) / 2) *
            (J + (1 / 2 : ℝ) * K) := hphase
      _ ≤ ((d : ℝ) / 2) * C :=
        mul_le_mul_of_nonneg_left hconstant (by positivity)
      _ = C * ((d : ℝ) / 2) := by ring
end CohnElkies
