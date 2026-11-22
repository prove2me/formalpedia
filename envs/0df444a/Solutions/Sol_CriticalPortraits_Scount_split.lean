-- Prove2me | solution 1 for CriticalPortraits.Scount_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:49.868575+00:00
-- url     : https://prove2.me/submissions/71ec3a39-e246-46b4-b5ee-534bae6e9a02

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} [NeZero (d * m)] {U : Finset (ZMod (d * m))} {x y : ℕ}
    {w : ZMod (d * m)}
    (hwU : w ∈ U) (hxw : x < w.val) (hwy : w.val < y) :
    Scount U x y = Scount U x w.val + 1 + Scount U w.val y := by
  classical
  unfold Scount
  -- the filter for (x,y) splits as (x,w) ∪ {w} ∪ (w,y)
  have hsplit : U.filter (fun t => x < t.val ∧ t.val < y)
      = U.filter (fun t => x < t.val ∧ t.val < w.val)
        ∪ {w}
        ∪ U.filter (fun t => w.val < t.val ∧ t.val < y) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨htU, htx, hty⟩
      rcases lt_trichotomy t.val w.val with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨htU, htx, hlt⟩)
      · exact Or.inl (Or.inr (ZMod.val_injective _ heq))
      · exact Or.inr ⟨htU, hgt, hty⟩
    · rintro (((⟨htU, htx, htw⟩) | rfl) | ⟨htU, htw, hty⟩)
      · exact ⟨htU, htx, lt_trans htw hwy⟩
      · exact ⟨hwU, hxw, hwy⟩
      · exact ⟨htU, lt_trans hxw htw, hty⟩
  rw [hsplit]
  -- the three parts are pairwise disjoint
  have hdisj1 : Disjoint (U.filter (fun t => x < t.val ∧ t.val < w.val))
      ({w} : Finset (ZMod (d * m))) := by
    simp_all
  have hdisj2 : Disjoint (U.filter (fun t => x < t.val ∧ t.val < w.val) ∪ {w})
      (U.filter (fun t => w.val < t.val ∧ t.val < y)) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter] at ha hb
      omega
    · simp_all
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    Finset.card_singleton]
end CriticalPortraits
