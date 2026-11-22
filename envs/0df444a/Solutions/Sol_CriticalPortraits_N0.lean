-- Prove2me | solution 1 for CriticalPortraits.N0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:35:03.792912+00:00
-- url     : https://prove2.me/submissions/0dcb78d8-0182-4dce-a098-d9d996b36a75

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
public import Theorems.Thm_CriticalPortraits_GPRE

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
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m)
    {t : ZMod (d * m)} (htU : t ∈ U)
    (hlo : (betaParent U u).val < t.val) (hhi : t.val < (betaParent U u).val + m) : False := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set φ := u.val % m with hφ
  set lu := u.val / m with hludef
  set K := betaK U u with hKdef
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  have hKle : K ≤ lu - 1 := betaK_le U u
  -- GPRE at j = K+1: Scount v (φ+(K+1)*m) ≤ 0
  have hj1 : K < K + 1 := by omega
  have hj2 : K + 1 ≤ lu := by omega
  have hgpre := GPRE hd hm hcanon hu hlu hj1 hj2
  -- (φ + (K+1)*m) = v + m
  have hwval : φ + (K + 1) * m = (betaParent U u).val + m := by
    rw [hpval]; ring
  rw [hwval] at hgpre
  -- hgpre : Scount v (v+m) ≤ (K+1) - K - 1 = 0
  have hzero : Scount U (betaParent U u).val ((betaParent U u).val + m) = 0 := by
    simp_all
  -- but t is in that window
  have htmem : t ∈ U.filter (fun w => (betaParent U u).val < w.val ∧
      w.val < (betaParent U u).val + m) := by
    rw [Finset.mem_filter]; exact ⟨htU, hlo, hhi⟩
  have hpos : 0 < Scount U (betaParent U u).val ((betaParent U u).val + m) := by
    unfold Scount
    exact Finset.card_pos.mpr ⟨t, htmem⟩
  omega
end CriticalPortraits
