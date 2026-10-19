-- Prove2me | solution 1 for CohnElkies.monotone_leftRiemann_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/d7521b43-bc43-4366-92c2-0ba2ae34c8cb

import Mathlib
import Definitions.Def_SpherePacking

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
    (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ≤
        f 1 - f 0 := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hscaled :
      MonotoneOn (fun x : ℝ => f (x / (k : ℝ)))
        (Icc (0 : ℝ) (k : ℝ)) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨div_nonneg hx.1 hkpos.le,
        (div_le_one hkpos).2 hx.2⟩
    · exact ⟨div_nonneg hy.1 hkpos.le,
        (div_le_one hkpos).2 hy.2⟩
    · exact div_le_div_of_nonneg_right hxy hkpos.le
  have hscaled' :
      MonotoneOn (fun x : ℝ => f (x / (k : ℝ)))
        (Icc (0 : ℝ) (0 + (k : ℝ))) := by
    simpa using! hscaled
  have hleft :
      (∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ))) ≤
        ∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ)) := by
    simpa using! (MonotoneOn.sum_le_integral
      (x₀ := (0 : ℝ)) (a := k) hscaled')
  have hright :
      (∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ))) ≤
        ∑ j ∈ Finset.range k,
          f (((j : ℝ) + 1) / (k : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using!
      (MonotoneOn.integral_le_sum
        (x₀ := (0 : ℝ)) (a := k) hscaled')
  have hintegral :
      (∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ))) =
        (k : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    simp [hkne]
  have hshift :
      (∑ j ∈ Finset.range k,
        f (((j : ℝ) + 1) / (k : ℝ))) -
        (∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ))) =
          f 1 - f 0 := by
    rw [← Finset.sum_sub_distrib]
    convert! Finset.sum_range_sub
      (fun j : ℕ => f ((j : ℝ) / (k : ℝ))) k using 1
    · apply Finset.sum_congr rfl
      intro j _
      simp [Nat.cast_add, Nat.cast_one]
    · simp [hkne]
  constructor
  · rw [← hintegral]
    linarith
  · rw [← hintegral]
    linarith
end CohnElkies
