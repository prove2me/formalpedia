-- Prove2me | solution 1 for CriticalPortraits.betaParent_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:52.451459+00:00
-- url     : https://prove2.me/submissions/ab4c0816-827c-4d16-8264-4585d1d30f6e

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
public import Theorems.Thm_CriticalPortraits_betaK_spec

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    (Scount U (betaParent U u).val u.val : ℤ)
      = ((u.val / m : ℕ) : ℤ) - ((betaK U u : ℕ) : ℤ) - 1 := by
  have hspec := betaK_spec hd hm hcanon hu hlu
  have hpval : (betaParent U u).val = u.val % m + betaK U u * m := by
    rw [betaParent_val hd hm hlu]; rfl
  unfold Defc at hspec
  rw [hpval]
  -- hspec : (Scount U (u.val%m + betaK U u * m) u.val : ℤ) - ((u.val/m) - betaK U u - 1) = 0
  linarith
end CriticalPortraits
