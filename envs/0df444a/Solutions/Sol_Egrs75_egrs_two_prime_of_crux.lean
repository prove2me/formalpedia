-- Prove2me | solution 1 for Egrs75.egrs_two_prime_of_crux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:03.600188+00:00
-- url     : https://prove2.me/submissions/91a5dba0-a90c-47cf-b350-3f69936a9fdf

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Theorems.Thm_Egrs75_not_dvd_centralBinom_iff_lowDigits


set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat
namespace Egrs75
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hcrux : EgrsCrux p q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by
  have hset :
      {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n} =
        {n : ℕ | LowDigits p n ∧ LowDigits q n} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    rw [not_dvd_centralBinom_iff_lowDigits hp hpo n,
        not_dvd_centralBinom_iff_lowDigits hq hqo n]
  rwa [hset]
end Egrs75
