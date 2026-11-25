-- Prove2me | solution 1 for Finset.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:04.18708+00:00
-- url     : https://prove2.me/submissions/213dacaa-095c-4d5f-8e81-e8cd49ceb07a

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {V : Type*} [DecidableEq V]
namespace Finset
theorem _root_.solution {s : Finset V} {v w : V} : s(v, w) ∈ s.pairs ↔ v ∈ s ∧ w ∈ s ∧ v ≠ w := by
  simp [pairs, mem_sym2_iff, and_assoc]
end Finset
