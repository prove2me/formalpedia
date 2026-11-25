-- Prove2me | solution 1 for Erdos699.le_pow_card_of_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:46.469658+00:00
-- url     : https://prove2.me/submissions/5694205d-ef4b-4a2a-b44f-f51a9e147602

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution {g n i : ℕ} (hn : n ≠ 0) (hg : g ≠ 0) (hin : i ≤ n)
    (hdvd : g ∣ n.choose i) : g ≤ n ^ g.primeFactors.card := by
  have hc : n.choose i ≠ 0 := (Nat.choose_pos hin).ne'
  calc g = g.factorization.prod (fun p k => p ^ k) := (Nat.prod_factorization_pow_eq_self hg).symm
    _ = ∏ p ∈ g.primeFactors, p ^ g.factorization p := by
        rw [Finsupp.prod, Nat.support_factorization]
    _ ≤ ∏ _p ∈ g.primeFactors, n := by
        refine Finset.prod_le_prod' (fun p hp => ?_)
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        calc p ^ g.factorization p ≤ p ^ (n.choose i).factorization p :=
              Nat.pow_le_pow_right hp'.pos ((Nat.factorization_le_iff_dvd hg hc).2 hdvd p)
          _ ≤ p ^ Nat.log p n := Nat.pow_le_pow_right hp'.pos Nat.factorization_choose_le_log
          _ ≤ n := Nat.pow_log_le_self p hn
    _ = n ^ g.primeFactors.card := Finset.prod_const n
end Erdos699
