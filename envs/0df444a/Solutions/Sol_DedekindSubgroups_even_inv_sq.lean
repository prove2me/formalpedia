-- Prove2me | solution 1 for DedekindSubgroups.even_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:10:17.246928+00:00
-- url     : https://prove2.me/submissions/a1626dc9-6ce9-44d5-a3e7-ad158576a9ef

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
public import Theorems.Thm_DedekindSubgroups_signAux_mulPerm
public import Theorems.Thm_DedekindSubgroups_one_lt_of_inv


set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution {g g' : ℕ} (hk : 0 < k) (hinv : g * g' % k = 1) :
    Even (inv (g * g % k) k) := by
  have hinv2 : (g * g % k) * (g' * g' % k) % k = 1 := by
    rw [← Nat.mul_mod, show g * g * (g' * g') = (g * g') * (g * g') by ring, Nat.mul_mod, hinv,
      one_mul]
    exact Nat.mod_eq_of_lt (one_lt_of_inv hk hinv)
  have hcomp : mulPerm hk hinv2 = mulPerm hk hinv * mulPerm hk hinv := by
    ext r
    simp only [mulPerm, Perm.coe_mul, Function.comp_apply, Equiv.coe_fn_mk, sig]
    rw [Nat.mod_mul_mod, Nat.mul_mod g, Nat.mod_mod, ← Nat.mul_mod, mul_assoc]
  have hs := signAux_mulPerm hk hinv2
  rw [hcomp, Perm.signAux_mul, Int.units_mul_self] at hs
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp hs.symm
end DedekindSubgroups
