-- Prove2me | solution 1 for Corless.IsSign.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:40.085356+00:00
-- url     : https://prove2.me/submissions/d0d9e549-abbc-42c6-9316-809e8e335deb

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
namespace IsSign
theorem _root_.solution {s : ℕ → ℤ} {m n : ℕ} (hs : IsSign s n) (hm : m ≤ n) : IsSign s m :=
  fun i hi => hs i (hi.trans_le hm)
end IsSign
end Corless
