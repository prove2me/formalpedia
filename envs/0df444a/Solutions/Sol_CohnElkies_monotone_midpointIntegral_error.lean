-- Prove2me | solution 1 for CohnElkies.monotone_midpointIntegral_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/39d04803-92a4-441e-924c-564ab02af572

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
    (f : ℝ → ℝ) (k : ℕ)
    (hf : MonotoneOn f (Icc (0 : ℝ) (k : ℝ))) :
    |(∫ x in (0 : ℝ)..(k : ℝ), f x) -
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2)| ≤
      f (k : ℝ) - f 0 := by
  have hf' : MonotoneOn f (Icc (0 : ℝ) (0 + (k : ℝ))) := by
    simpa using! hf
  have hleft :
      (∑ j ∈ Finset.range k, f (j : ℝ)) ≤
        ∫ x in (0 : ℝ)..(k : ℝ), f x := by
    simpa using!
      (MonotoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := k) hf')
  have hright :
      (∫ x in (0 : ℝ)..(k : ℝ), f x) ≤
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using!
      (MonotoneOn.integral_le_sum (x₀ := (0 : ℝ)) (a := k) hf')
  have hmidleft :
      (∑ j ∈ Finset.range k, f (j : ℝ)) ≤
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hjlast : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hjk)
    exact hf ⟨hjnonneg, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hmidright :
      (∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2)) ≤
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hjlast : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hjk)
    exact hf ⟨by linarith, by linarith⟩
      ⟨by linarith, hjlast⟩ (by linarith)
  have hshift :
      (∑ j ∈ Finset.range k, f ((j : ℝ) + 1)) -
        (∑ j ∈ Finset.range k, f (j : ℝ)) =
          f (k : ℝ) - f 0 := by
    rw [← Finset.sum_sub_distrib]
    convert! Finset.sum_range_sub (fun j : ℕ => f (j : ℝ)) k using 1
    · apply Finset.sum_congr rfl
      intro j _
      simp [Nat.cast_add, Nat.cast_one]
    · simp
  apply (abs_le).2
  constructor <;> linarith
end CohnElkies
