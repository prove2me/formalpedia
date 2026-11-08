-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_geometric_not_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:44:16.113095+00:00
-- url     : https://prove2.me/submissions/b145115c-294f-4910-a28e-6bedf8d5bef7

import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_power_cell_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- A dyadic singular generator loss is not integrable under geometric law. -/
theorem solution
    (p : unitInterval) (hp : p != 0) (hhalf : (p : Real) = 1 / 2)
    (y : Nat -> Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (Integrable (fun k : Nat =>
      -(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k)))
      (geometricMeasure p)) := by
  let g : Nat -> Real := fun k =>
    -(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))
  intro hi
  have hpne : p ≠ 0 := by
    intro heq
    simp [heq] at hp
  have hs : Summable (fun k : Nat =>
      (1 - (p : Real)) ^ k * (p : Real) * ‖g k‖) :=
    (ProbabilityTheory.integrable_geometricMeasure_iff hpne).1 hi
  have hbound : forall k : Nat, (2 : Real) ^ k <= g k := by
    intro k
    exact AvramDividend.Classical.avram_a19_singular_power_cell_bound
      k (y k) (hy k) (hsmall k) (hpower k)
  have hterm : forall k : Nat, (1 / 2 : Real) <=
      (1 - (p : Real)) ^ k * (p : Real) * ‖g k‖ := by
    intro k
    have hpow : 0 < (2 : Real) ^ k := pow_pos (by norm_num) _
    have hg : 0 <= g k := le_trans (le_of_lt hpow) (hbound k)
    have hnorm : ‖g k‖ = g k := by
      rw [Real.norm_eq_abs, abs_of_nonneg hg]
    have hdiv : (1 : Real) <= g k / (2 : Real) ^ k :=
      (le_div_iff₀ hpow).2 (by nlinarith [hbound k])
    calc
      (1 / 2 : Real) = (1 / 2 : Real) * 1 := by ring
      _ <= (1 / 2 : Real) * (g k / (2 : Real) ^ k) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = (1 - (p : Real)) ^ k * (p : Real) * ‖g k‖ := by
        rw [hhalf, hnorm]
        have hh : (1 : Real) - 1 / 2 = 1 / 2 := by ring
        rw [hh, one_div_pow]
        ring
  have hsconst : Summable (fun _ : Nat => (1 / 2 : Real)) :=
    Summable.of_nonneg_of_le (fun _ => by norm_num) hterm hs
  have hzero : (1 / 2 : Real) = 0 := (summable_const_iff (1 / 2 : Real)).1 hsconst
  norm_num at hzero
