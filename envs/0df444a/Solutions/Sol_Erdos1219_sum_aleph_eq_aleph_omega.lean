-- Prove2me | solution 1 for Erdos1219.sum_aleph_eq_aleph_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:35.900814+00:00
-- url     : https://prove2.me/submissions/75b4ff52-f111-4819-856f-9a75c13e1782

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Theorems.Thm_Erdos1219_aleph_nat_le_aleph_omega
import Theorems.Thm_Erdos1219_aleph_omega_le_of_forall_nat

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution (e : ℕ → ℕ) (he : ∀ N, N ≤ e N) :
    Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u})) = ℵ_ ω := by
  apply le_antisymm
  · calc Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u}))
        ≤ Cardinal.sum (fun _ : ℕ => (ℵ_ ω : Cardinal.{u})) :=
          sum_le_sum _ _ fun p => aleph_nat_le_aleph_omega (e p)
      _ = ℵ_ ω := by
          rw [sum_const]
          simp only [mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id']
          exact mul_eq_right (aleph0_le_aleph ω) (aleph0_le_aleph ω) aleph0_ne_zero
  · refine aleph_omega_le_of_forall_nat fun N => ?_
    calc ℵ_ (N : Ordinal.{u}) ≤ ℵ_ (e N : Ordinal.{u}) := aleph_le_aleph.2 (by exact_mod_cast he N)
      _ ≤ _ := le_sum _ N
end Erdos1219
