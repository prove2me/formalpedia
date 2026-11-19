-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:40:56.820207+00:00
-- url     : https://prove2.me/submissions/7f437ad9-9082-43eb-a0c0-8fee81758028

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_weighted_signed_potential_drop_sum_swap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
noncomputable section

theorem solution
    {ι : Type*} (s : Finset ι)
    (E : ι → ℝ) (pre post : ι → ℝ) (w V : ℝ → ℝ)
    (initial final : ℝ)
    (hInit : V initial = w initial)
    (hFinal : V final = w final)
    (hPost : ∀ i ∈ s, V (post i) = w (post i)) :
    (w initial - w final) +
      (∑ i ∈ s, E i * (w (post i) - w (pre i))) =
    (V initial - V final) -
      (∑ i ∈ s, E i * (V (pre i) - V (post i))) +
      (∑ i ∈ s, E i * (V (pre i) - w (pre i))) := by
  have hsum :
      (∑ i ∈ s, E i * (w (post i) - w (pre i))) =
        -(∑ i ∈ s, E i * (V (pre i) - V (post i))) +
        (∑ i ∈ s, E i * (V (pre i) - w (pre i))) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hPost i hi]
    ring
  rw [← hInit, ← hFinal, hsum]
  ring
