-- Prove2me | solution 1 for DerivativeChainPrefixLaws.scaled_sequence_contraction
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:32:45.106331+00:00
-- url     : https://prove2.me/submissions/bfd83116-fbcd-4502-a87b-2e018f6a3cf9

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
open DerivativeChainPrefixLaws












theorem solution (V : ℕ → ℝ) (n h : ℕ) (hh : h ≤ n)
    (hstep : ∀ k<n, (k+1:ℝ)*V k ≤ (k:ℝ)*V (k+1)) :
    (n:ℝ)*V h ≤ (h:ℝ)*V n := by
  induction n with
  | zero =>
    have he : h=0 := by omega
    subst h
    simp
  | succ n ih =>
    by_cases he : h=n+1
    · subst h; exact le_rfl
    have hh' : h ≤ n := by omega
    by_cases hn : n=0
    · subst n
      have he : h=0 := by omega
      subst h
      simpa only [Nat.cast_zero,Nat.cast_one,zero_add,one_mul,zero_mul] using hstep 0 (by omega)
    have hnR : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hi := ih hh' (fun k hk => hstep k (by omega))
    have hs := hstep n (by omega)
    have H : (n:ℝ)*((n+1:ℝ)*V h) ≤ (n:ℝ)*((h:ℝ)*V (n+1)) := by
      calc
        _ = (n+1:ℝ)*((n:ℝ)*V h) := by ring
        _ ≤ (n+1:ℝ)*((h:ℝ)*V n) := mul_le_mul_of_nonneg_left hi (by positivity)
        _ = (h:ℝ)*((n+1:ℝ)*V n) := by ring
        _ ≤ (h:ℝ)*((n:ℝ)*V (n+1)) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg h)
        _ = _ := by ring
    simpa only [Nat.cast_add,Nat.cast_one] using (mul_le_mul_iff_of_pos_left hnR).mp H
