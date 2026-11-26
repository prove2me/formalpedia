-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:36.524103+00:00
-- url     : https://prove2.me/submissions/defb23fe-cadb-41e7-b4c1-afce9db5351a

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {k : ℕ} (hk : 0 < k) (ks : List ℕ) :
    syracuseNumeratorList (k :: ks) % 2 = 1 := by
  rw [syracuseNumeratorList_cons, Nat.add_mod, Nat.mul_mod]
  have hthree : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ, Nat.mul_mod, ih]
  have hpow : 2 ^ k % 2 = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ, Nat.mul_mod]
    norm_num
  rw [hthree, hpow]
  simp
end CollatzEndpointTransport.FixedTotal
