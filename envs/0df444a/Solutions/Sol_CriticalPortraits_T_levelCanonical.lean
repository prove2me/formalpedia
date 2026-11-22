-- Prove2me | solution 1 for CriticalPortraits.T_levelCanonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:47.566634+00:00
-- url     : https://prove2.me/submissions/d7a8cedf-1585-4318-80c5-105fce4c5fad

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Theorems.Thm_AbstractLaminar_master

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    LevelCanonical d m (T P) := by
  have : NeZero (d*m) := ⟨by positivity⟩
  intro j hj
  -- The LevelCanonical filter equals `contained (survivorFamily) 0 j`.
  have hfilter : (T P).filter (fun i => i.val / m ≤ j)
      = AbstractLaminar.contained (survivorFamily hd hm hP) 0 j := by
    unfold AbstractLaminar.contained
    apply Finset.filter_congr
    intro e he
    constructor
    · intro h; exact ⟨Nat.zero_le _, h⟩
    · intro h; exact h.2
  rw [hfilter]
  have hm0 := AbstractLaminar.master (survivorFamily hd hm hP) 0 j
  unfold AbstractLaminar.N at hm0
  simpa using hm0
end CriticalPortraits
