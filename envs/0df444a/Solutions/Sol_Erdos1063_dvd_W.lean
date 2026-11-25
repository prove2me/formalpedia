-- Prove2me | solution 1 for Erdos1063.dvd_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:35:48.357165+00:00
-- url     : https://prove2.me/submissions/94197cf0-3457-4800-8f17-76fdc01201b3

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) : k ∣ W k := by
  unfold W
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hk]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  rw [Nat.factorization_def k (Nat.prime_of_mem_primeFactors hp)]
  exact pow_dvd_pow p (Nat.le_add_right _ _)
end Erdos1063
