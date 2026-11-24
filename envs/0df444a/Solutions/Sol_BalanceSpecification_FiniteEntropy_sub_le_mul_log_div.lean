-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.sub_le_mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:11.573195+00:00
-- url     : https://prove2.me/submissions/aa5aa93f-a830-4c24-bf49-d58554683022

module
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : p ≠ 0 → 0 < q) : p - q ≤ p * Real.log (p / q) := by
  by_cases hz : p = 0
  · simp only [hz, zero_sub, zero_mul]
    exact neg_nonpos.mpr hq
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hqp := hsupport hz
  have hlog := Real.log_le_sub_one_of_pos (div_pos hqp hpp)
  calc
    p - q = (-p) * (q / p - 1) := by field_simp; ring
    _ ≤ (-p) * Real.log (q / p) :=
      mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hp)
    _ = p * Real.log (p / q) := by
      rw [Real.log_div hqp.ne' hz, Real.log_div hz hqp.ne']
      ring
end BalanceSpecification.FiniteEntropy
