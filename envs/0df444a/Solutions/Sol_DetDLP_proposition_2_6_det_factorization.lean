-- Prove2me | solution 1 for DetDLP.proposition_2_6_det_factorization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:46:45.937274+00:00
-- url     : https://prove2.me/submissions/486c8d5e-9e4b-4dcf-86ca-b9b37a0fd792
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_Machine
import Theorems.Thm_DetDLP_bounded_divisor_search_from_btn
import Theorems.Thm_DetDLP_factor_splitting_driver_machine
import Theorems.Thm_DetDLP_theorem_2_2_btn_contraction
import Theorems.Thm_DetDLP_lemma_2_3_mult_gadget

namespace DetDLP.Factor

private def split (f : ℕ → ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
    let d := f x
    if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x/d) else [x])

private theorem split_perm (f : ℕ → ℕ)
    (hf : ∀ x : ℕ, 2 ≤ x → ¬ x.Prime → 2 ≤ f x ∧ f x < x ∧ f x ∣ x)
    (k x : ℕ) (hx : 2 ≤ x) (hk : x < 2^(k+1)) :
    (split f k x).Perm x.primeFactorsList := by
  induction k generalizing x with
  | zero => simp at hk; omega
  | succ k ih =>
    let d := f x
    by_cases h : 2 ≤ d ∧ d < x ∧ d ∣ x
    · have hd0 : 0 < d := by omega
      have heq : d*(x/d) = x := Nat.mul_div_cancel' h.2.2
      have hother : 2 ≤ x/d := by
        by_contra! hle
        have hmul := Nat.mul_le_mul_left d (show x/d ≤ 1 by omega)
        omega
      have half1 : 2*d ≤ x := by rw [← heq,Nat.mul_comm 2]; exact Nat.mul_le_mul_left d hother
      have half2 : 2*(x/d) ≤ x := by simpa only [heq] using Nat.mul_le_mul_right (x/d) h.1
      rw [pow_succ] at hk
      have hd := ih d h.1 (by omega)
      have he := ih (x/d) hother (by omega)
      change List.Perm (if 2 ≤ d ∧ d < x ∧ d ∣ x then split f k d ++ split f k (x/d) else [x]) _
      rw [if_pos h]
      apply (hd.append he).trans
      simpa only [heq] using (Nat.perm_primeFactorsList_mul hd0.ne' (show x/d ≠ 0 by omega)).symm
    · have hp : x.Prime := by by_contra he; exact h (hf x hx he)
      change List.Perm (if 2 ≤ d ∧ d < x ∧ d ∣ x then split f k d ++ split f k (x/d) else [x]) _
      rw [if_neg h,Nat.primeFactorsList_prime hp]

private theorem split_sorted (f : ℕ → ℕ)
    (hf : ∀ x : ℕ, 2 ≤ x → ¬ x.Prime → 2 ≤ f x ∧ f x < x ∧ f x ∣ x)
    (x : ℕ) (hx : 2 ≤ x) :
    ((split f (bitLen (x+1)) x).mergeSort) = x.primeFactorsList := by
  let k := bitLen (x+1)
  have hk' : x+1 ≤ 2^k := Nat.le_pow_clog (by decide) _
  have hk : x < 2^(k+1) := by rw [pow_succ]; omega
  have h := split_perm f hf k x hx hk
  apply ((List.mergeSort_perm _ _).trans h).eq_of_pairwise' (r := (· ≤ ·))
  · exact List.pairwise_mergeSort' _ _
  · exact (Nat.primeFactorsList_sorted _).pairwise
end DetDLP.Factor

open DetDLP


open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


theorem solution :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) := by
  obtain ⟨f,Md,od,Kd,hd⟩ := bounded_divisor_search_from_btn theorem_2_2_btn_contraction lemma_2_3_mult_gadget
  obtain ⟨M,out,K,hr⟩ := factor_splitting_driver_machine f Md od Kd (fun N h => (hd N h).2)
  refine ⟨M,out,K,?_⟩
  intro N hN n
  have run := hr N hN
  change RunsWithin M out (countWord N) (encodeNatListBin ((Factor.split f n N).mergeSort)) _ _ at run
  rwa [Factor.split_sorted f (fun x hx => (hd x hx).1) N hN] at run
