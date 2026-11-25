-- Prove2me | solution 1 for Finset.pairs_eq_image_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:33.055054+00:00
-- url     : https://prove2.me/submissions/180c19b9-3161-49cf-8d08-f7435bfe5225

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
public import Theorems.Thm_Finset_mem_pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {V : Type*} [DecidableEq V]
namespace Finset
theorem _root_.solution (s : Finset V) : s.pairs = s.offDiag.image Sym2.mk.uncurry := by
  ext e
  induction e using Sym2.ind with
  | _ v w =>
    rw [mem_pairs, mem_image]
    constructor
    · rintro ⟨hv, hw, hvw⟩
      exact ⟨(v, w), mem_offDiag.mpr ⟨hv, hw, hvw⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, h⟩
      obtain ⟨ha, hb, hne⟩ := mem_offDiag.mp hab
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ha, hb, hne⟩
      · exact ⟨hb, ha, Ne.symm hne⟩
end Finset
