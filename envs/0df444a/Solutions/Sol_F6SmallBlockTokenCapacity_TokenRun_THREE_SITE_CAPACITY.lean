-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.THREE_SITE_CAPACITY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:55:45.624804+00:00
-- url     : https://prove2.me/submissions/0aee0fcb-7c41-4b34-b3b1-6526e3eb82ff

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_THREE_SITE_INCIDENCE_EQUALITY
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_THREE_STEP_RETURN

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (R : TokenRun B W q) (hB : Fintype.card B ≤ 3) :
    q ≤ 2 := by
  classical
  by_contra hq
  have hthree : 3 ≤ q := by omega
  let P := R.firstSteps 3 hthree
  obtain ⟨hcard, hs, hc⟩ := R.THREE_SITE_INCIDENCE_EQUALITY hB hthree
  obtain ⟨x, hx0, hx1, hx2, hreturn⟩ := THREE_STEP_RETURN P hcard hs hc
  have hw0 : P.rank x (P.state 0 x) < P.rank x (P.state 1 x) := P.HWORSE 0 x hx0
  have hout1 : P.state 1 x = P.state 2 x := P.HOUT 1 x hx1
  have hw2 : P.rank x (P.state 2 x) < P.rank x (P.state 3 x) := P.HWORSE 2 x hx2
  rw [← hout1, hreturn] at hw2
  exact lt_asymm hw0 hw2
end F6SmallBlockTokenCapacity.TokenRun
