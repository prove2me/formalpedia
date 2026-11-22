-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.labels_eq_of_jointLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:32.303239+00:00
-- url     : https://prove2.me/submissions/13eaab83-0e74-4f89-b3ab-f2b1aa602f72

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_label_local

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hfr : ∀ i, T.Fresh W i)
    {t : ℕ} (e : Edge W t) {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (hi' : i + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    (hj' : j + deletionMargin k (Fintype.card S) ≤ e.endDepth)
    (heq : jointLabel T e j = jointLabel T e i)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : e.TraversedBy o) :
    label T W t o.1 (depthCut W t o j) = label T W t o.1 (depthCut W t o i) := by
  rw [label_local hfr e ho hth hj hj', label_local hfr e ho hth hi hi']
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  exact Prod.ext h1 (congrFun h2 _)
end DeciSigma1.Holes.Fresh
