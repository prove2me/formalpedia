-- Prove2me | solution 1 for Finset.disjoint_smul_mulStab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:50.038652+00:00
-- url     : https://prove2.me/submissions/4570fcb3-a56b-4036-802b-9677cc477cf0

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Theorems.Thm_Finset_mulStab_mul_ssubset_mulStab
public import Theorems.Thm_Finset_mulStab_union
public import Theorems.Thm_Finset_mul_aux1

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
namespace Finset
theorem _root_.solution (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose has
  exact subset_trans has hst
end Finset
