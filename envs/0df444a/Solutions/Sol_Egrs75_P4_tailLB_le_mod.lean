-- Prove2me | solution 1 for Egrs75.P4.tailLB_le_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:56.553217+00:00
-- url     : https://prove2.me/submissions/01a92e55-3683-4531-a17f-a0c8fb211db5

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Theorems.Thm_Egrs75_P4_middle_digit_eq
public import Theorems.Thm_Egrs75_P4_mod_pow_succ

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
namespace Egrs75.P4
theorem _root_.solution {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n)
    {t : ℕ} (htlo : topBadIndex q n < t) (hthi : t ≤ leastGoodAbove hq hbad) :
    tailLB q n (topBadIndex q n) t ≤ n % q ^ t := by
  set j := topBadIndex q n with hj
  -- induct on `t` from `j+1`.  Reformulate as: ∀ d, j+1+d ≤ i → tailLB (j+1+d) ≤ mod.
  obtain ⟨d, rfl⟩ : ∃ d, t = j + 1 + d := ⟨t - (j + 1), by omega⟩
  clear htlo
  induction d with
  | zero =>
    -- base: t = j+1.  tailLB = b_j·q^j (empty Ico sum); n % q^{j+1} ≥ q^j·b_j.
    simp only [tailLB, Nat.add_zero]
    have hIco : Finset.Ico (j + 1) (j + 1) = (∅ : Finset ℕ) := by simp
    rw [hIco, Finset.sum_empty, Nat.mul_zero, Nat.add_zero]
    rw [mod_pow_succ n q j, Nat.mul_comm (q ^ j) (n / q ^ j % q)]
    exact Nat.le_add_left _ _
  | succ d ih =>
    -- step: t = j+1+(d+1).  Need j+1+d < i to apply middle_digit_eq at index j+1+d.
    have hstep_hi : j + 1 + d ≤ leastGoodAbove hq hbad := by omega
    have hstep_lt : j + 1 + d < leastGoodAbove hq hbad := by omega
    have ih' := ih (by omega)
    -- middle digit at index (j+1+d) is exactly B:
    have hmid : n / q ^ (j + 1 + d) % q = (q - 1) / 2 :=
      middle_digit_eq hq hbad (by omega) hstep_lt
    -- tailLB at t+1 = tailLB at t + B·q^(j+1+d)
    have htail_succ : tailLB q n j (j + 1 + (d + 1))
        = tailLB q n j (j + 1 + d) + ((q - 1) / 2) * q ^ (j + 1 + d) := by
      simp only [tailLB]
      rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega,
          Finset.sum_Ico_succ_top (by omega : j + 1 ≤ j + 1 + d) (fun s => q ^ s)]
      ring
    -- mod at t+1 = mod at t + q^(j+1+d)·B
    have hmod_succ : n % q ^ (j + 1 + (d + 1))
        = n % q ^ (j + 1 + d) + q ^ (j + 1 + d) * ((q - 1) / 2) := by
      rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega, mod_pow_succ n q (j + 1 + d), hmid]
    rw [htail_succ, hmod_succ]
    have hcomm : ((q - 1) / 2) * q ^ (j + 1 + d) = q ^ (j + 1 + d) * ((q - 1) / 2) := by
      rw [Nat.mul_comm]
    omega
end Egrs75.P4
