-- Prove2me | solution 2 for CohnElkies.monotone_midpointIntegral_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:01.028559+00:00
-- url     : https://prove2.me/submissions/99636880-414b-4178-9b0b-d79b1a80b445

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


theorem solution
    (f : ℝ → ℝ) (k : ℕ)
    (hf : MonotoneOn f (Icc (0 : ℝ) (k : ℝ))) :
    |(∫ x in (0 : ℝ)..(k : ℝ), f x) -
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2)| ≤
      f (k : ℝ) - f 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc] at hf ⊢
    have hn0 : (0:ℝ) ≤ n := n.cast_nonneg
    have hmono' : MonotoneOn f (Icc 0 (n:ℝ)) := hf.mono (Icc_subset_Icc_right (by linarith))
    have ih' := ih hmono'
    have hI1 : IntervalIntegrable f volume 0 (n:ℝ) := by
      apply MonotoneOn.intervalIntegrable; rw [uIcc_of_le hn0]; exact hmono'
    have hI2 : IntervalIntegrable f volume (n:ℝ) (n+1) := by
      apply MonotoneOn.intervalIntegrable; rw [uIcc_of_le (by linarith)]
      exact hf.mono (Icc_subset_Icc_left hn0)
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, Finset.sum_range_succ]
    have hmem : ∀ x ∈ Icc (n:ℝ) (n+1), x ∈ Icc (0:ℝ) (n+1) := fun x hx => ⟨by linarith [hx.1], hx.2⟩
    have hlo : f n ≤ ∫ x in (n:ℝ)..(n+1), f x := by
      have := intervalIntegral.integral_mono_on (by linarith : (n:ℝ) ≤ n+1) intervalIntegrable_const hI2
        (fun x hx => hf (hmem n ⟨le_rfl, by linarith⟩) (hmem x hx) hx.1)
      simpa using this
    have hhi : ∫ x in (n:ℝ)..(n+1), f x ≤ f (n+1) := by
      have := intervalIntegral.integral_mono_on (by linarith : (n:ℝ) ≤ n+1) hI2 intervalIntegrable_const
        (fun x hx => hf (hmem x hx) (hmem (n+1) ⟨by linarith, le_rfl⟩) hx.2)
      simpa using this
    have hm1 : f n ≤ f (n + 1/2) :=
      hf (by constructor <;> linarith) (by constructor <;> linarith) (by linarith)
    have hm2 : f (n + 1/2) ≤ f (n+1) :=
      hf (by constructor <;> linarith) (by constructor <;> linarith) (by linarith)
    rw [abs_le] at ih' ⊢
    constructor <;> linarith [ih'.1, ih'.2]

