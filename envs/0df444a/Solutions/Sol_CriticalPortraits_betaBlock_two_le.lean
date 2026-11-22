-- Prove2me | solution 1 for CriticalPortraits.betaBlock_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:38.556276+00:00
-- url     : https://prove2.me/submissions/91affd11-1d88-47db-8171-ae3ccb8a9dba

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
public import Theorems.Thm_CriticalPortraits_mem_bVerts_of_mem
public import Theorems.Thm_CriticalPortraits_betaParent_mem_bVerts

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {v : ZMod (d * m)}
    (hv : v ∈ bVerts U) : 2 ≤ (betaBlock U v).card := by
  have : NeZero (d*m) := ⟨by positivity⟩
  -- find a U-point u with u in the block (u = v if v ∈ U, else v = betaParent u)
  rcases Finset.mem_union.mp hv with hvU | hvImg
  · -- v ∈ U: block contains v and betaParent v, distinct
    have hlu := survivor_level_pos hd hcanon hvU
    have hp_mem : betaParent U v ∈ betaBlock U v := by
      rw [mem_betaBlock]
      refine ⟨betaParent_mem_bVerts hvU, ?_⟩
      exact Relation.ReflTransGen.single (Or.inr ⟨hvU, hlu, rfl⟩)
    have hv_mem : v ∈ betaBlock U v := by rw [mem_betaBlock]; exact ⟨hv, bReach_refl v⟩
    have hne : betaParent U v ≠ v := by
      intro h
      have hlt : (betaParent U v).val < v.val := betaParent_val_lt hd hm hlu
      rw [h] at hlt; omega
    have hsub : ({betaParent U v, v} : Finset (ZMod (d*m))) ⊆ betaBlock U v := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h <;> subst h
      · exact hp_mem
      · exact hv_mem
    have hcard2 : ({betaParent U v, v} : Finset (ZMod (d*m))).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hne
    calc 2 = ({betaParent U v, v} : Finset (ZMod (d*m))).card := hcard2.symm
      _ ≤ (betaBlock U v).card := Finset.card_le_card hsub
  · -- v ∈ image(betaParent): v = betaParent u, u ∈ U; block contains v and u
    rw [Finset.mem_image] at hvImg
    obtain ⟨u, huU, hvu⟩ := hvImg
    have hlu := survivor_level_pos hd hcanon huU
    have hu_mem : u ∈ betaBlock U v := by
      rw [mem_betaBlock]
      refine ⟨mem_bVerts_of_mem huU, ?_⟩
      -- v = betaParent u, so bAdj v u (bEdge U v u)
      rw [← hvu]
      exact Relation.ReflTransGen.single (Or.inl ⟨huU, hlu, rfl⟩)
    have hv_mem : v ∈ betaBlock U v := by rw [mem_betaBlock]; exact ⟨hv, bReach_refl v⟩
    have hne : u ≠ v := by
      intro h
      have hlt : (betaParent U u).val < u.val := betaParent_val_lt hd hm hlu
      rw [hvu, h] at hlt; omega
    have hsub : ({u, v} : Finset (ZMod (d*m))) ⊆ betaBlock U v := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h <;> subst h
      · exact hu_mem
      · exact hv_mem
    have hcard2 : ({u, v} : Finset (ZMod (d*m))).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hne
    calc 2 = ({u, v} : Finset (ZMod (d*m))).card := hcard2.symm
      _ ≤ (betaBlock U v).card := Finset.card_le_card hsub
end CriticalPortraits
