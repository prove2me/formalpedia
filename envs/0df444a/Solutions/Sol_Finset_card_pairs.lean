-- Prove2me | solution 1 for Finset.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:15.70316+00:00
-- url     : https://prove2.me/submissions/9171c237-09b3-488a-be45-d148a54de337

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
public import Theorems.Thm_Finset_pairs_eq_image_offDiag

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {V : Type*} [DecidableEq V]
namespace Finset
theorem _root_.solution (s : Finset V) : #s.pairs = (#s).choose 2 := by
  rw [pairs_eq_image_offDiag, Sym2.card_image_offDiag]
end Finset
