-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.fresh_of_mortal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:05.551419+00:00
-- url     : https://prove2.me/submissions/fc25103e-7c8e-426a-8da7-f033554a0456

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_immortal_of_not_fresh

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}
namespace DeciSigma1.Readers.StructuralReader
theorem _root_.solution [DecidableEq S] {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i)
    (hm : ¬ M.Immortal (M.endState W i)) : M.Fresh W i := by
  by_contra hf
  exact hm (immortal_of_not_fresh h hf)
end DeciSigma1.Readers.StructuralReader
