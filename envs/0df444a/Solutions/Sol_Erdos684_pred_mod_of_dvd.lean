-- Prove2me | solution 1 for Erdos684.pred_mod_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:40:09.272876+00:00
-- url     : https://prove2.me/submissions/4023599f-62c4-4ec6-9ceb-a9d955f8f52b

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {M q : ℕ} (hM : 0 < M) (_hq : 0 < q) (hdiv : q ∣ M) :
    (M - 1) % q = q - 1 := by
  obtain ⟨t, rfl⟩ := hdiv
  simpa using Nat.mul_sub_mod (n := q) (p := t) (x := 0) hM
end Erdos684
