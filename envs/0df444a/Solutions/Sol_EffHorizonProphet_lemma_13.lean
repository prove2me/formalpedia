-- Prove2me | solution 1 for EffHorizonProphet.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:24:43.583422+00:00
-- url     : https://prove2.me/submissions/bf091fed-481f-48e6-a78f-5aa360a052b2

import Mathlib
import Definitions.Def_EffHorizonProphet_truncGeomMoment

namespace Aux_EffHorizonProphet_lemma_13

lemma ident (r : ℝ) (S : ℕ) :
    (1 - r) * ∑ j ∈ Finset.range S, (j : ℝ) ^ 1 * r ^ j + S * r ^ S
      = r * ∑ j ∈ Finset.range S, r ^ j := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    linear_combination ih

end Aux_EffHorizonProphet_lemma_13

open EffHorizonProphet in
theorem solution (S : ℕ) (hS : 1 ≤ S) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    truncGeomMoment S r 1 ≤ r / (1 - r) := by
  unfold truncGeomMoment
  have hG : 0 < ∑ j ∈ Finset.range S, r ^ j := by
    have h0 : (0 : ℕ) ∈ Finset.range S := Finset.mem_range.mpr (by omega)
    calc (0 : ℝ) < r ^ 0 := by norm_num
      _ ≤ ∑ j ∈ Finset.range S, r ^ j :=
        Finset.single_le_sum (f := fun j => r ^ j) (fun j _ => pow_nonneg hr0 j) h0
  have hid := Aux_EffHorizonProphet_lemma_13.ident r S
  have hpos : 0 ≤ (S : ℝ) * r ^ S := by positivity
  rw [div_le_div_iff₀ hG (by linarith)]
  nlinarith
