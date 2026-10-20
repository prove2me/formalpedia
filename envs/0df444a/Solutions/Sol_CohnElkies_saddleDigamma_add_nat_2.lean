-- Prove2me | solution 2 for CohnElkies.saddleDigamma_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:43:31.432857+00:00
-- url     : https://prove2.me/submissions/8f9e6d26-4b7d-4408-9e99-e870bb8a5354

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {m : ℝ} (hm : 0 < m) (n : ℕ) :
    saddleDigamma (m + (n : ℝ)) =
      saddleDigamma m +
        ∑ k ∈ Finset.range n,
          (m + (k : ℝ))⁻¹ := by
  have key : ∀ x : ℝ, 0 < x → saddleDigamma (x + 1) = saddleDigamma x + x⁻¹ := by
    intro x hx
    unfold saddleDigamma
    have hdG : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma (fun m h => by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
    have hd : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x :=
      (Real.differentiableAt_log (Real.Gamma_pos_of_pos hx).ne').comp x hdG
    have heq : (fun y => (Real.log ∘ Real.Gamma) (y + 1)) =ᶠ[nhds x] (fun y => Real.log y + (Real.log ∘ Real.Gamma) y) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp only [Function.comp]
      rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
    have h1 : deriv (fun y => (Real.log ∘ Real.Gamma) (y + 1)) x = deriv (Real.log ∘ Real.Gamma) (x + 1) :=
      deriv_comp_add_const _ _ _
    have h2 : HasDerivAt (fun y => Real.log y + (Real.log ∘ Real.Gamma) y) (x⁻¹ + deriv (Real.log ∘ Real.Gamma) x) x :=
      (Real.hasDerivAt_log hx.ne').add hd.hasDerivAt
    rw [← h1, heq.deriv_eq, h2.deriv]
    ring
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, key _ (by positivity), ih, Finset.sum_range_succ]
    ring

