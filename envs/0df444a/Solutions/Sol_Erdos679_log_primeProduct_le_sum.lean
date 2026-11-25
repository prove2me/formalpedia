-- Prove2me | solution 1 for Erdos679.log_primeProduct_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:33.031262+00:00
-- url     : https://prove2.me/submissions/6698f8d1-733f-44d7-bb6f-69630839b76b

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_log_primeProduct
public import Theorems.Thm_Erdos679_sum_log_succ

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N)
    (hp : ∀ i ≥ N, (Nat.nth Nat.Prime i : ℝ) ≤ (3 / 2 : ℝ) * i * log i)
    {m : ℕ} (hm : N ≤ m) (hlog : 1 ≤ log m) :
    log (primeProduct m : ℝ) ≤ log (primeProduct N : ℝ) + log (m.factorial : ℝ) +
      m * (log (3 / 2 : ℝ) + log (log m)) := by
  let g : ℕ → ℝ := fun i => log ((i + 1 : ℕ) : ℝ) +
    (log (3 / 2 : ℝ) + log (log m))
  have hgnonneg (i : ℕ) : 0 ≤ g i := by
    dsimp [g]
    exact add_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)))
      (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hlog))
  have htail : ∑ i ∈ Finset.Ico N m, log (Nat.nth Nat.Prime i) ≤
      ∑ i ∈ Finset.Ico N m, g i := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hiN, him⟩ := Finset.mem_Ico.mp hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    have himr : (i : ℝ) ≤ m := by exact_mod_cast him.le
    have hli : 0 ≤ log (i : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ i by omega))
    have hlim : log (i : ℝ) ≤ log m := Real.log_le_log hi0 himr
    have hsize : (Nat.nth Nat.Prime i : ℝ) ≤
        (3 / 2 : ℝ) * (i + 1) * log m := by
      apply (hp i hiN).trans
      apply mul_le_mul
      · nlinarith
      · exact hlim
      · exact hli
      · positivity
    have hplog := Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime i).pos) hsize
    rw [Real.log_mul (by positivity) (by linarith),
      Real.log_mul (by norm_num) (by positivity)] at hplog
    dsimp [g]
    push_cast
    linarith
  have hprefix : 0 ≤ ∑ i ∈ Finset.range N, g i :=
    Finset.sum_nonneg fun i _ => hgnonneg i
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => log (Nat.nth Nat.Prime i)) hm
  have hgsplit := Finset.sum_range_add_sum_Ico g hm
  have hgsum : ∑ i ∈ Finset.range m, g i =
      log (m.factorial : ℝ) + m * (log (3 / 2 : ℝ) + log (log m)) := by
    simp only [g, Finset.sum_add_distrib, sum_log_succ, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rw [log_primeProduct, log_primeProduct]
  linarith
end Erdos679
