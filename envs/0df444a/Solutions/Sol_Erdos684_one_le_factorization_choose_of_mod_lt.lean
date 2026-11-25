-- Prove2me | solution 1 for Erdos684.one_le_factorization_choose_of_mod_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:39:59.024454+00:00
-- url     : https://prove2.me/submissions/6dad2b26-b648-4a3f-8923-ecf4203090e3

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
public import Theorems.Thm_Erdos684_factorization_choose_pos_of_mod_lt

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) :
    1 ≤ (n.choose k).factorization p :=
  factorization_choose_pos_of_mod_lt hp hkn hmod
end Erdos684
