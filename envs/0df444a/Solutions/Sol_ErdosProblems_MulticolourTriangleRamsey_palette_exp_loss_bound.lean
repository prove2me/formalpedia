-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.palette_exp_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/d00b349d-5a28-46ee-a6aa-a7567b89a992

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H a s : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hs : 0 < s)
    (hlogH : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) ≤
      ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hepos : 0 < Real.exp 1 ^ 2 * (a : ℝ) ^ 2 := by positivity
  have hbasepos : 0 < (H : ℝ) / Real.exp 1 := by positivity
  have htargetpos :
      0 < ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) := by positivity
  have hsourcepos :
      0 < ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by
    positivity
  have hloga : Real.log (a : ℝ) ≤ (a : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hapos
  have hlogs : Real.log (s : ℝ) ≤ (s : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hspos
  have hweightedH :
      (s : ℝ) * Real.log (H : ℝ) ≤ (s : ℝ) * (a : ℝ) :=
    mul_le_mul_of_nonneg_left hlogH hspos.le
  have hweightedA :
      2 * (s : ℝ) * Real.log (a : ℝ) ≤
        2 * (s : ℝ) * ((a : ℝ) - 1) := by
    gcongr
  have hcore :
      (a : ℝ) * (s : ℝ) * (Real.log (H : ℝ) - 4) +
          Real.log (s : ℝ) +
          (s : ℝ) * (2 + 2 * Real.log (a : ℝ)) ≤
        ((a : ℝ) - 1) * (s : ℝ) *
          (Real.log (H : ℝ) - 1) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hcore hHpos.le
  have htargetlog :
      Real.log (((H : ℝ) / Real.exp 4) ^ (H * (a * s))) =
        (H : ℝ) * (a : ℝ) * (s : ℝ) *
          (Real.log (H : ℝ) - 4) := by
    rw [Real.log_pow,
      Real.log_div hHpos.ne' (Real.exp_ne_zero 4), Real.log_exp]
    push_cast
    ring
  have hsourcelog :
      Real.log
          (((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
            ((s : ℝ) ^ H *
              (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H))) =
        (H : ℝ) * ((a : ℝ) - 1) * (s : ℝ) *
            (Real.log (H : ℝ) - 1) -
          ((H : ℝ) * Real.log (s : ℝ) +
            (s : ℝ) * (H : ℝ) *
              (2 + 2 * Real.log (a : ℝ))) := by
    rw [Real.log_div
      (pow_ne_zero _ hbasepos.ne')
      (mul_ne_zero (pow_ne_zero _ hspos.ne') (pow_ne_zero _ hepos.ne'))]
    rw [Real.log_pow,
      Real.log_div hHpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
    rw [Real.log_mul (pow_ne_zero _ hspos.ne') (pow_ne_zero _ hepos.ne'),
      Real.log_pow, Real.log_pow]
    rw [Real.log_mul (pow_ne_zero _ (Real.exp_ne_zero 1))
      (pow_ne_zero _ hapos.ne'), Real.log_pow, Real.log_exp, Real.log_pow]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    ring
  apply (Real.log_le_log_iff htargetpos hsourcepos).mp
  rw [htargetlog, hsourcelog]
  nlinarith
end ErdosProblems.MulticolourTriangleRamsey
