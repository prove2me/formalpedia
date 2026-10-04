-- Prove2me | solution 1 for CookPvsNP.stack_bounded_loop
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:46.623795+00:00
-- url     : https://prove2.me/submissions/8d92fc92-646e-4a11-b967-1243775a02f3

import Definitions.Def_CookPvsNP_StackProgram

set_option autoImplicit false
open CookPvsNP

private theorem loop_exec {K A : Type} (test : (K → Option A) → Bool) (p : StackProg K A)
    (n : ℕ) (s : ℕ → K → List A) (cost : ℕ → ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, p.Exec (s i) (s (i + 1)) (cost i)) :
    (StackProg.loop test p).Exec (s 0) (s n)
      ((∑ i ∈ Finset.range n, (cost i + 2)) + 1) := by
  induction n generalizing s cost with
  | zero => simpa using StackProg.Exec.loopFalse he
  | succ n ih =>
    have hh := ih (fun i => s (i + 1)) (fun i => cost (i + 1))
      (fun i hi => hg (i + 1) (by omega)) he (fun i hi => hb (i + 1) (by omega))
    have hx := StackProg.Exec.loopTrue (hg 0 (by omega)) (hb 0 (by omega)) hh
    convert hx using 1
    rw [Finset.sum_range_succ']
    omega

theorem solution {K A : Type} (test : (K → Option A) → Bool) (p : StackProg K A)
    (n : ℕ) (s : ℕ → K → List A) (cost : ℕ → ℕ) (B : ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, p.Exec (s i) (s (i + 1)) (cost i))
    (hc : ∀ i < n, cost i ≤ B) :
    ∃ t ≤ n * (B + 2) + 1, (StackProg.loop test p).Exec (s 0) (s n) t := by
  refine ⟨(∑ i ∈ Finset.range n, (cost i + 2)) + 1, ?_, loop_exec test p n s cost hg he hb⟩
  have h : (∑ i ∈ Finset.range n, (cost i + 2)) ≤ ∑ _i ∈ Finset.range n, (B + 2) :=
    Finset.sum_le_sum (fun i hi => Nat.add_le_add_right (hc i (Finset.mem_range.mp hi)) 2)
  simpa using Nat.add_le_add_right h 1

#print axioms solution
