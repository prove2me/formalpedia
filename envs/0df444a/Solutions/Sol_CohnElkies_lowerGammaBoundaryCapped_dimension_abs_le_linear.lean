-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_dimension_abs_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/a5c00d72-da3b-4664-acc8-9426536fdb09

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_continuous
import Theorems.Thm_CohnElkies_harmonic_dimensionGammaBoundary_abs_le_linear

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
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ,
        |lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y| ≤
            A * (1 + |y|) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A₀, hA₀, htail⟩ :=
    harmonic_dimensionGammaBoundary_abs_le_linear d R
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc : IsCompact
      (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
        (lowerGammaBoundaryCapped_continuous
          hℓ R D).continuousOn
  let A : ℝ :=
    max 0 (max K (max |D| A₀))
  have hA : 0 ≤ A := le_max_left _ _
  have hKA : K ≤ A :=
    le_trans (le_max_left _ _)
      (le_max_right _ _)
  have hDA : |D| ≤ A :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_max_right _ _))
  have hA₀A : A₀ ≤ A :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_max_right _ _))
  refine ⟨A, hA, ?_⟩
  intro y
  have hfactor : 1 ≤ 1 + |y| := by
    linarith [abs_nonneg y]
  by_cases hy : |y| < 2
  · have hymem : y ∈ Icc (-2 : ℝ) 2 := by
      have hbounds := abs_lt.mp hy
      exact ⟨hbounds.1.le, hbounds.2.le⟩
    have hcompact := hK y hymem
    rw [Real.norm_eq_abs] at hcompact
    calc
      |lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y| ≤ K := hcompact
      _ ≤ A := hKA
      _ ≤ A * (1 + |y|) := by
        nlinarith [mul_nonneg hA (abs_nonneg y)]
  · have hylarge : 2 ≤ |y| := le_of_not_gt hy
    have hyzero : y ≠ 0 := by
      intro heq
      subst y
      norm_num at hylarge
    unfold lowerGammaBoundaryCapped
    rw [if_neg hyzero]
    by_cases hmin :
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y ≤ D
    · rw [min_eq_left hmin]
      calc
        |lowerGammaBoundaryLog
          ((d : ℝ) / 2) R y| ≤
            A₀ * (1 + |y|) := htail y hylarge
        _ ≤ A * (1 + |y|) :=
          mul_le_mul_of_nonneg_right hA₀A
            (by positivity)
    · rw [min_eq_right (le_of_not_ge hmin)]
      calc
        |D| ≤ A := hDA
        _ ≤ A * (1 + |y|) := by
          nlinarith [mul_nonneg hA (abs_nonneg y)]
end CohnElkies
