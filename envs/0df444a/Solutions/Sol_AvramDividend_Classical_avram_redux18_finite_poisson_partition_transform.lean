-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_finite_poisson_partition_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:02:32.036835+00:00
-- url     : https://prove2.me/submissions/02afadf0-49c4-4f52-841f-60782c1644aa

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_avram_redux18_poisson_weighted_count_transform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-! The independent finite-bin Poisson generating factors exponentiate additively. -/
theorem solution
    {ι : Type*} (s : Finset ι) (rate q : ι → ℝ) :
    s.prod (fun i =>
      (∑' m : ℕ, Real.exp (-(rate i)) *
        ((rate i) ^ m / (m.factorial : ℝ)) *
        Real.exp (-(m : ℝ) * q i))) =
    Real.exp (s.sum (fun i => rate i * (Real.exp (-(q i)) - 1))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        AvramDividend.Classical.avram_redux18_poisson_weighted_count_transform
          (rate a) (q a), ih, Real.exp_add]