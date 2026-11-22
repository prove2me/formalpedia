-- Prove2me | solution 1 for CriticalPortraits.root_val_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:06.339451+00:00
-- url     : https://prove2.me/submissions/c2ee8b1f-bb25-43fc-a5e9-b620bdb78a7a

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
public import Theorems.Thm_CriticalPortraits_sep_master


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
    {g x : ZMod (d * m)} (hg : g ∈ T P) (hx : x ∈ T P)
    (hlo : loV P x ≤ loV P g) (hhi : hiV g ≤ hiV x) (hcol : colV g ≠ colV x) : g.val < x.val := by
  have hgv := top_val_eq (x := g)
  have hxv := top_val_eq (x := x)
  rcases lt_or_eq_of_le hhi with hlt | heq
  · have := sep_master (m := m) (p := colV g) (q := colV x) (colV_lt_m hm g) (colV_lt_m hm x) hlt
    omega
  · -- hiV g = hiV x.  Then loV P x < loV P g (else equal edges → g = x → colV g = colV x).
    have hlostrict : loV P x < loV P g := by
      rcases lt_or_eq_of_le hlo with h | h
      · exact h
      · exact absurd (edge_inj hd hm hP hx hg h heq.symm) (fun hxg => hcol (by rw [hxg]))
    have hcg : colV g < colV x := lemmaB_right hd hm hP hx hg heq.symm hlostrict
    simp_all
end CriticalPortraits
