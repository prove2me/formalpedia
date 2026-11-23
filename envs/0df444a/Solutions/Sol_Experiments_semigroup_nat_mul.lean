-- Prove2me | solution 1 for Experiments.semigroup_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:06.0721+00:00
-- url     : https://prove2.me/submissions/fa0d2f1e-88f8-4c07-96b3-e61cc77b73fc

import Mathlib
import Definitions.Def_Experiments_GeneratorBound

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
namespace Experiments
theorem _root_.solution {E : Type*} [Monoid E] (M : ℝ → E) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    M ((n : ℝ) * h) = M h ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Nat.cast_add_one, add_mul, one_mul,
      hadd _ _ (mul_nonneg (Nat.cast_nonneg n) hh) hh, ih, pow_succ]
end Experiments
