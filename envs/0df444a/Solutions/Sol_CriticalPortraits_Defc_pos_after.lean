-- Prove2me | solution 1 for CriticalPortraits.Defc_pos_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:52.757627+00:00
-- url     : https://prove2.me/submissions/d2880449-8b94-49b4-9f7e-f537c40cea58

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
public import Theorems.Thm_CriticalPortraits_discrete_ivt
public import Theorems.Thm_CriticalPortraits_Defc_step
public import Theorems.Thm_CriticalPortraits_Defc_top_nonneg
public import Theorems.Thm_CriticalPortraits_betaK_max

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (_hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (_hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (_hu : u ∈ U) (hlu : 1 ≤ u.val / m) {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m - 1) :
    0 < Defc U (u.val % m) (u.val / m) u.val j := by
  classical
  set φ := u.val % m with hφ
  set lu := u.val / m with hludef
  by_contra hle
  push Not at hle
  -- shifted sequence E i := D (j + i), defined on [0, (lu-1) - j]
  set L := (lu - 1) - j with hLdef
  set E : ℕ → ℤ := fun i => Defc U φ lu u.val (j + i) with hEdef
  have hE0 : E 0 ≤ 0 := by simpa [hEdef] using hle
  have hEL : 0 ≤ E L := by
    have : j + L = lu - 1 := by omega
    simp only [hEdef]
    rw [this]
    exact Defc_top_nonneg U φ lu u.val hlu
  have hEstep : ∀ i, i < L → E (i+1) ≤ E i + 1 := by
    intro i _
    simp only [hEdef]
    have : j + (i + 1) = (j + i) + 1 := by omega
    rw [this]
    exact Defc_step hm U φ lu u.val (j + i)
  obtain ⟨i, hiL, hEi⟩ := discrete_ivt E L hE0 hEL hEstep
  -- j + i is a zero of D, with K < j ≤ j + i ≤ lu - 1
  have hzero : Defc U φ lu u.val (j + i) = 0 := by simpa [hEdef] using hEi
  have hKlt : betaK U u < j + i := by omega
  have hle_lu : j + i ≤ lu - 1 := by omega
  exact betaK_max hKlt hle_lu hzero
end CriticalPortraits
