-- Prove2me | solution 1 for CriticalPortraits.bridge_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:36:58.858197+00:00
-- url     : https://prove2.me/submissions/d9fc534c-db83-4c9f-b3a0-2b5b32061275

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_CriticalPortraits_column_sep_geom
public import Theorems.Thm_AbstractLaminar_rootS_contains
public import Theorems.Thm_AbstractLaminar_rootS_mem_E
public import Theorems.Thm_AbstractLaminar_rootS_mem_Roots
public import Theorems.Thm_AbstractLaminar_rootS_window


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u b2 : ZMod (d * m)} (hu : u ∈ T P) (hb2 : b2 ∈ T P)
    (hcol : colV b2 = colV u)
    (hlo : loV P u < loV P b2) (hhi : hiV b2 < hiV u) :
    ∃ g ∈ T P, colV g ≠ colV u ∧
      loV P u ≤ loV P g ∧ loV P g ≤ loV P b2 ∧ hiV b2 ≤ hiV g ∧ hiV g ≤ hiV u ∧ g ≠ b2 := by
  set fam := survivorFamily hd hm hP with hfam
  -- window of u's edge
  have hwin : loV P u < hiV u := by
    change fam.lo u < fam.hi u; exact fam.lh u hu
  -- b2 ∈ Sstrict of u's window (strictly nested: lo ≠ loV u OR hi ≠ hiV u — both hold)
  have hb2cont : b2 ∈ AbstractLaminar.contained fam (loV P u) (hiV u) := by
    rw [AbstractLaminar.mem_contained]
    refine ⟨hb2, by change loV P u ≤ loV P b2; omega, by change hiV b2 ≤ hiV u; omega⟩
  have hb2S : b2 ∈ AbstractLaminar.Sstrict fam (loV P u) (hiV u) := by
    rw [AbstractLaminar.mem_Sstrict]
    refine ⟨⟨hb2, by change loV P u ≤ loV P b2; omega, by change hiV b2 ≤ hiV u; omega⟩, ?_⟩
    left; change loV P b2 ≠ loV P u; omega
  -- g := rootS of b2 in u's window
  set g := AbstractLaminar.rootS fam (loV P u) (hiV u) b2 with hg
  have hgRoot : g ∈ AbstractLaminar.Roots fam (loV P u) (hiV u) :=
    AbstractLaminar.rootS_mem_Roots fam hb2S
  have hgE : g ∈ T P := AbstractLaminar.rootS_mem_E fam hb2S
  have hgwin := AbstractLaminar.rootS_window fam hb2S
  have hgcont := AbstractLaminar.rootS_contains fam hb2S
  -- column separation: col g ≠ col u
  have hgcol : colV g ≠ colV u := column_sep_geom hd hm hP hu hwin g hgRoot
  -- g ≠ b2 : equal edges (same col impossible since col g ≠ col u = col b2)
  have hgb2 : g ≠ b2 := by
    intro h; rw [h] at hgcol; exact hgcol hcol
  refine ⟨g, hgE, hgcol, ?_, ?_, ?_, ?_, hgb2⟩
  · exact hgwin.1
  · exact hgcont.1
  · exact hgcont.2
  · exact hgwin.2
end CriticalPortraits
