-- Prove2me | solution 1 for CohnElkies.exists_antiFourierWitness_eventually_capped_bottom_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/410b9848-062a-460b-97ca-487d6b329a49

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_uniform_bound
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_bottom_norm_le_gamma

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ y : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp (lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y) := by
  obtain ⟨C, hC, hglobal⟩ :=
    antiFourierWitness_normalizedMellinStrip_uniform_bound hd w
  let D₀ : ℝ := Real.log (C + 1)
  have hD₀ : Real.exp D₀ = C + 1 := by
    try dsimp [D₀]
    apply Real.exp_log
    linarith
  refine ⟨D₀, ?_⟩
  intro D hD y
  have hbounded :
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ C := by
    apply hglobal
    · simp
    · simp
      have hdim : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
  have hcapped :
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp D := by
    calc
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ C :=
        hbounded
      _ ≤ C + 1 := by linarith
      _ = Real.exp D₀ := hD₀.symm
      _ ≤ Real.exp D := Real.exp_le_exp.mpr hD
  by_cases hy : y = 0
  · subst y
    simpa [lowerGammaBoundaryCapped] using! hcapped
  · unfold lowerGammaBoundaryCapped
    rw [if_neg hy]
    by_cases hmin :
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y ≤ D
    · rw [min_eq_left hmin]
      exact
        antiFourierWitness_normalizedMellinStrip_bottom_norm_le_gamma
          hd hR w y hy
    · rw [min_eq_right (le_of_not_ge hmin)]
      exact hcapped
end CohnElkies
