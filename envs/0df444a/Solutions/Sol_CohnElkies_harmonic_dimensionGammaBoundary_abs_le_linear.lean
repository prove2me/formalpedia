-- Prove2me | solution 1 for CohnElkies.harmonic_dimensionGammaBoundary_abs_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/8fb27e75-5947-4190-aaee-37ecbe17a467

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_harmonic_integerGammaBoundary_abs_le_linear
import Theorems.Thm_CohnElkies_harmonic_halfIntegerGammaBoundary_abs_le_linear
import Theorems.Thm_CohnElkies_harmonic_dimensionGammaBoundary_eq_abs

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
    (d : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ, 2 ≤ |y| →
        |lowerGammaBoundaryLog
          ((d : ℝ) / 2) R y| ≤
          A * (1 + |y|) := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hcast :
        ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    obtain ⟨A, hA, htail⟩ :=
      harmonic_integerGammaBoundary_abs_le_linear k R
    refine ⟨A, hA, ?_⟩
    intro y hy
    have hyzero : y ≠ 0 := by
      intro heq
      subst y
      norm_num at hy
    rw [harmonic_dimensionGammaBoundary_eq_abs R hyzero,
      hcast]
    exact htail |y| hy
  · have hcast :
        ((↑(2 * k + 1) : ℝ) / 2) =
          (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    obtain ⟨A, hA, htail⟩ :=
      harmonic_halfIntegerGammaBoundary_abs_le_linear k R
    refine ⟨A, hA, ?_⟩
    intro y hy
    have hyzero : y ≠ 0 := by
      intro heq
      subst y
      norm_num at hy
    rw [harmonic_dimensionGammaBoundary_eq_abs R hyzero,
      hcast]
    exact htail |y| hy
end CohnElkies
