-- Prove2me | solution 1 for BalanceSpecification.renewal_le_pow_of_pressure_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:54.756074+00:00
-- url     : https://prove2.me/submissions/04af4966-2ac5-4208-8ee8-2a19e2ba06d7

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
    {a g : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hg : ∀ n : ℕ, 0 ≤ g n)
    (ha0 : a 0 ≤ 1)
    (hrec : ∀ n : ℕ, a (n + 1) ≤
      ∑ l ∈ Finset.range (n + 1), g (l + 1) * a (n - l))
    (hpressure : ∀ n : ℕ,
      (∑ l ∈ Finset.range (n + 1), g (l + 1) / ρ ^ (l + 1)) ≤ 1)
    (n : ℕ) : a n ≤ ρ ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [pow_zero] using ha0
    | succ n =>
      have hterm l (hl : l ∈ Finset.range (n + 1)) :
          g (l + 1) * ρ ^ (n - l) =
            ρ ^ (n + 1) * (g (l + 1) / ρ ^ (l + 1)) := by
        have hln : l ≤ n := by have H := Finset.mem_range.mp hl; omega
        have hpow : ρ ^ (n - l) * ρ ^ (l + 1) = ρ ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [← mul_div_assoc]
        apply (eq_div_iff (pow_ne_zero _ hρ.ne')).mpr
        calc
          (g (l + 1) * ρ ^ (n - l)) * ρ ^ (l + 1) =
              g (l + 1) * (ρ ^ (n - l) * ρ ^ (l + 1)) := mul_assoc _ _ _
          _ = g (l + 1) * ρ ^ (n + 1) := by rw [hpow]
          _ = ρ ^ (n + 1) * g (l + 1) := mul_comm _ _
      calc
        a (n + 1) ≤ ∑ l ∈ Finset.range (n + 1), g (l + 1) * a (n - l) := hrec n
        _ ≤ ∑ l ∈ Finset.range (n + 1), g (l + 1) * ρ ^ (n - l) := by
          apply Finset.sum_le_sum
          intro l hl
          exact mul_le_mul_of_nonneg_left (ih (n - l) (by omega)) (hg (l + 1))
        _ = ∑ l ∈ Finset.range (n + 1),
            ρ ^ (n + 1) * (g (l + 1) / ρ ^ (l + 1)) := Finset.sum_congr rfl hterm
        _ = ρ ^ (n + 1) *
            (∑ l ∈ Finset.range (n + 1), g (l + 1) / ρ ^ (l + 1)) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ ρ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (hpressure n) (pow_nonneg hρ.le _)
        _ = ρ ^ (n + 1) := mul_one _
end BalanceSpecification
