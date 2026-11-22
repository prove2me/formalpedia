-- Prove2me | solution 1 for CriticalPortraits.Scount_bot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:26.744836+00:00
-- url     : https://prove2.me/submissions/cd200aba-a26e-438a-b45f-41c7ccc4278a

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
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) :
    Scount U (u.val % m) u.val ≤ u.val / m - 1 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  -- key arithmetic facts about u.val
  have hdm : u.val % m + (u.val / m) * m = u.val := Nat.mod_add_div' u.val m
  have hφ : u.val % m < m := Nat.mod_lt _ hm
  have hlud : u.val / m < d := by
    have hlt : u.val < d * m := ZMod.val_lt u
    by_contra hge
    push Not at hge
    have : d * m ≤ (u.val / m) * m := Nat.mul_le_mul_right m hge
    omega
  -- {t : φ < t.val < u.val} ⊆ filter (level ≤ lu) \ {u}
  have hsub : U.filter (fun t => u.val % m < t.val ∧ t.val < u.val)
      ⊆ (U.filter (fun i => i.val / m ≤ u.val / m)).erase u := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htU, _, htlt⟩ := ht
    rw [Finset.mem_erase, Finset.mem_filter]
    have htlevel : t.val / m ≤ u.val / m := by
      have hdiv : t.val / m * m ≤ t.val := Nat.div_mul_le_self t.val m
      by_contra hgt
      push Not at hgt
      have : (u.val / m + 1) ≤ t.val / m := hgt
      have h2 : (u.val / m + 1) * m ≤ (t.val / m) * m := Nat.mul_le_mul_right m this
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega
    refine ⟨?_, htU, htlevel⟩
    intro htu; rw [htu] at htlt; omega
  have humem : u ∈ U.filter (fun i => i.val / m ≤ u.val / m) := by
    rw [Finset.mem_filter]; exact ⟨hu, le_refl _⟩
  have hcard1 : (U.filter (fun t => u.val % m < t.val ∧ t.val < u.val)).card
      ≤ ((U.filter (fun i => i.val / m ≤ u.val / m)).erase u).card := Finset.card_le_card hsub
  have hcard2 : ((U.filter (fun i => i.val / m ≤ u.val / m)).erase u).card
      = (U.filter (fun i => i.val / m ≤ u.val / m)).card - 1 :=
    Finset.card_erase_of_mem humem
  have hcanon_lu : (U.filter (fun i => i.val / m ≤ u.val / m)).card ≤ u.val / m :=
    hcanon (u.val / m) hlud
  unfold Scount
  omega
end CriticalPortraits
