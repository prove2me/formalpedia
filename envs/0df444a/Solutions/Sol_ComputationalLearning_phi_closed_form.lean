-- Prove2me | solution 1 for ComputationalLearning.phi_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:14:47.625573+00:00
-- url     : https://prove2.me/submissions/803c6c6a-7b90-44d0-bbb0-11af084893a2

import Mathlib
import Definitions.Def_ComputationalLearning_VC

set_option autoImplicit false

open MeasureTheory

open ComputationalLearning in
theorem solution (d m : ℕ) :
    Phi d m = ∑ i ∈ Finset.range (d + 1), m.choose i := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => simp [Phi]
    | succ d =>
      rw [Finset.sum_range_succ']
      simp [Phi]
  | succ m ih =>
    cases d with
    | zero => simp [Phi]
    | succ d =>
      have e : Phi (d + 1) (m + 1) = Phi (d + 1) m + Phi d m := rfl
      rw [e, ih, ih, Finset.sum_range_succ' (fun i => (m + 1).choose i)]
      simp only [Nat.choose_succ_succ', Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun i => m.choose i) (d + 1)]
      simp only [Nat.choose_zero_right]
      ring
