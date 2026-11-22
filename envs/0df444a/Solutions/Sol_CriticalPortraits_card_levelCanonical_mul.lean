-- Prove2me | solution 1 for CriticalPortraits.card_levelCanonical_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:30.053229+00:00
-- url     : https://prove2.me/submissions/c6502377-c87a-453a-8bd7-38dee4f2b2ec

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
open _root_.CriticalPortraits.Cycle
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    d * Fintype.card {S : Finset (ZMod (d * m)) // S.card = d - 1 ∧ LevelCanonical d m S}
      = (d * m).choose (d - 1) := by
  have : NeZero (d * m) := ⟨by positivity⟩
  -- card Asub = card Csub * d  via the bijection
  have hbij : Fintype.card (Asub d m) = Fintype.card (Csub d m × Fin d) :=
    Fintype.card_congr (equivCanFin hd hm)
  rw [Fintype.card_prod, Fintype.card_fin] at hbij
  -- card Asub = C(d*m, d-1)
  have hA : Fintype.card (Asub d m) = (d * m).choose (d - 1) := by
    simp_all
  -- combine
  rw [hA] at hbij
  -- hbij : C(d*m,d-1) = card Csub * d
  rw [Nat.mul_comm d _]
  exact hbij.symm
end CriticalPortraits
