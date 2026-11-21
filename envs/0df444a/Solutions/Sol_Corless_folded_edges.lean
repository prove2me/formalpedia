-- Prove2me | solution 1 for Corless.folded_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:26.689185+00:00
-- url     : https://prove2.me/submissions/21b7fd83-b400-4a77-861f-b62f6ff564a2

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Theorems.Thm_Corless_folded_sizes

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution (k : ℕ) : 2 ^ (k + 2) - 2 = 2 * (2 ^ (k + 1) - 2) + 2 := by
  have full := (folded_sizes k).2
  omega
end Corless
