-- Prove2me | solution 1 for Finset.pairs_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:00:24.862305+00:00
-- url     : https://prove2.me/submissions/4501ba6e-bd66-4e0f-9a78-215f1260ac4d

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
theorem _root_.solution {s t : Finset V} (h : s ⊆ t) : s.pairs ⊆ t.pairs :=
  filter_subset_filter _ (sym2_mono h)
end Finset
