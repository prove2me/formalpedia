-- Prove2me | solution 1 for BalanceSpecification.convolution_le_pow_of_weighted_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:06.436733+00:00
-- url     : https://prove2.me/submissions/d2995a22-bdb2-4e2f-ac54-86aaf0148665

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_RenewalBounds

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    {a b : ℕ → ℝ} {ρ B : ℝ} (hρ : 0 < ρ) (hb : ∀ n : ℕ, 0 ≤ b n)
    (ha : ∀ n : ℕ, a n ≤ ρ ^ n)
    (hsum : ∀ n : ℕ, (∑ l ∈ Finset.range (n + 1), b l / ρ ^ l) ≤ B)
    (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), b l * a (n - l)) ≤ B * ρ ^ n := by
  have hterm l (hl : l ∈ Finset.range (n + 1)) :
      b l * ρ ^ (n - l) = ρ ^ n * (b l / ρ ^ l) := by
    have hln : l ≤ n := by have H := Finset.mem_range.mp hl; omega
    rw [← mul_div_assoc]
    apply (eq_div_iff (pow_ne_zero _ hρ.ne')).mpr
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hln, mul_comm]
  calc
    (∑ l ∈ Finset.range (n + 1), b l * a (n - l)) ≤
        ∑ l ∈ Finset.range (n + 1), b l * ρ ^ (n - l) :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (ha _) (hb l))
    _ = ∑ l ∈ Finset.range (n + 1), ρ ^ n * (b l / ρ ^ l) := Finset.sum_congr rfl hterm
    _ = ρ ^ n * (∑ l ∈ Finset.range (n + 1), b l / ρ ^ l) := (Finset.mul_sum _ _ _).symm
    _ ≤ ρ ^ n * B := mul_le_mul_of_nonneg_left (hsum n) (pow_nonneg hρ.le _)
    _ = B * ρ ^ n := mul_comm _ _
end BalanceSpecification
