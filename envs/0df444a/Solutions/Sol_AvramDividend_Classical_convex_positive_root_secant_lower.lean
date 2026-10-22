-- Prove2me | solution 1 for AvramDividend.Classical.convex_positive_root_secant_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:59:44.487701+00:00
-- url     : https://prove2.me/submissions/a60481bc-452c-48f0-b5d8-8835ff0f490d

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Convexity bounds the increment beyond a positive-height root
    by the secant slope from the origin. -/
theorem solution
    (f : ℝ → ℝ) (q φ θ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hzero : f 0 = 0) (hroot : f φ = q) :
    (q / φ) * θ ≤ f (φ + θ) - q := by
  have hsum : 0 < φ + θ := add_pos hφ hθ
  have hlt : φ < φ + θ := lt_add_of_pos_right φ hθ
  have hmφ : φ ∈ (Ici (0 : ℝ)) \ {0} := by
    simp only [mem_diff, mem_Ici, mem_singleton_iff]
    exact ⟨hφ.le, ne_of_gt hφ⟩
  have hmsum : φ + θ ∈ (Ici (0 : ℝ)) \ {0} := by
    simp only [mem_diff, mem_Ici, mem_singleton_iff]
    exact ⟨hsum.le, ne_of_gt hsum⟩
  have hmono := hconv.slope_mono (by simp : (0 : ℝ) ∈ Ici 0)
  have hs : slope f 0 φ ≤ slope f 0 (φ + θ) :=
    hmono hmφ hmsum hlt.le
  have hsa : slope f 0 φ = q / φ := by
    rw [slope_def_field, hzero, hroot]
    ring
  have hsb : slope f 0 (φ + θ) = f (φ + θ) / (φ + θ) := by
    rw [slope_def_field, hzero]
    ring
  rw [hsa, hsb] at hs
  have hcross : q * (φ + θ) ≤ f (φ + θ) * φ :=
    (div_le_div_iff₀ hφ hsum).mp hs
  have hid : (q / φ) * θ + q = q * (φ + θ) / φ := by
    field_simp [ne_of_gt hφ]
    ring
  apply (le_sub_iff_add_le).2
  rw [hid]
  exact (div_le_iff₀ hφ).2 (by nlinarith [hcross])
