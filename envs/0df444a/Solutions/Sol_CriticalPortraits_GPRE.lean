-- Prove2me | solution 1 for CriticalPortraits.GPRE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:26.231584+00:00
-- url     : https://prove2.me/submissions/5f0cc23a-1fa5-48d7-a117-065bf3bbf137

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
public import Theorems.Thm_CriticalPortraits_betaParent_balance
public import Theorems.Thm_CriticalPortraits_Defc_pos_after
public import Theorems.Thm_CriticalPortraits_Scount_add_le

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
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m) :
    (Scount U (betaParent U u).val (u.val % m + j * m) : ℤ) ≤ (j : ℤ) - (betaK U u : ℤ) - 1 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set φ := u.val % m with hφ
  set lu := u.val / m with hludef
  set K := betaK U u with hKdef
  -- v = betaParent val = φ + K*m
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  -- w' = φ + j*m, and v ≤ w' ≤ u.val
  have hvw : (betaParent U u).val ≤ φ + j * m := by
    rw [hpval]
    have : K * m ≤ j * m := Nat.mul_le_mul_right m (le_of_lt hj1)
    omega
  have hwu : φ + j * m ≤ u.val := by
    have hdm : φ + lu * m = u.val := by rw [hφ, hludef]; exact Nat.mod_add_div' u.val m
    have : j * m ≤ lu * m := Nat.mul_le_mul_right m hj2
    omega
  -- additive: Scount v w' + Scount w' u ≤ Scount v u
  have hadd := Scount_add_le U hvw hwu
  -- balance identity: Scount v u = lu - K - 1
  have hbal := betaParent_balance hd hm hcanon hu hlu
  -- Scount w' u ≥ lu - j (Defc_pos_after for j<lu; trivial for j=lu)
  have hsuf : (lu : ℤ) - (j : ℤ) ≤ (Scount U (φ + j * m) u.val : ℤ) := by
    rcases lt_or_eq_of_le hj2 with hjlt | hjeq
    · -- j < lu
      have hjle : j ≤ lu - 1 := by omega
      have hpos := Defc_pos_after hd hm hcanon hu hlu hj1 hjle
      unfold Defc at hpos
      -- hpos : 0 < Scount U (φ + j*m) u.val - (lu - j - 1)
      push_cast at hpos ⊢
      linarith
    · -- j = lu: w' = u.val, Scount = 0
      simp_all
  -- combine
  push_cast at hadd hbal ⊢
  linarith
end CriticalPortraits
