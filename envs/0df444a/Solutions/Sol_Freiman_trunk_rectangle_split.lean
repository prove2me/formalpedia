-- Prove2me | solution 1 for Freiman.trunk_rectangle_split
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:25:41.201821+00:00
-- url     : https://prove2.me/submissions/bf009d4e-1376-4f2f-89ab-ab46e7b7f9ad

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (R : CertRectangle) (axis : Bool) (hR : certRectangleValid R) (r s : ℝ) (hm : certRectangleMem R r s) :
    (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
    (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s) := by
  obtain ⟨h1, h2⟩ := hR
  obtain ⟨m1, m2, m3, m4⟩ := hm
  have h1' : (R.r0:ℝ) < R.r1 := by exact_mod_cast h1
  have h2' : (R.s0:ℝ) < R.s1 := by exact_mod_cast h2
  cases axis
  · -- r-axis split
    have e0 : trunkRectangleHalf R false false = ⟨R.r0,(R.r0+R.r1)/2,R.s0,R.s1⟩ := rfl
    have e1 : trunkRectangleHalf R false true = ⟨(R.r0+R.r1)/2,R.r1,R.s0,R.s1⟩ := rfl
    rw [e0, e1]
    refine ⟨⟨⟨?_, h2⟩, ⟨?_, h2⟩⟩, ?_⟩
    · show R.r0 < (R.r0+R.r1)/2
      linarith
    · show (R.r0+R.r1)/2 < R.r1
      linarith
    · rcases le_or_gt r (((R.r0+R.r1)/2 : ℚ) : ℝ) with h | h
      · left; exact ⟨m1, h, m3, m4⟩
      · right; exact ⟨h.le, m2, m3, m4⟩
  · -- s-axis split
    have e0 : trunkRectangleHalf R true false = ⟨R.r0,R.r1,R.s0,(R.s0+R.s1)/2⟩ := rfl
    have e1 : trunkRectangleHalf R true true = ⟨R.r0,R.r1,(R.s0+R.s1)/2,R.s1⟩ := rfl
    rw [e0, e1]
    refine ⟨⟨⟨h1, ?_⟩, ⟨h1, ?_⟩⟩, ?_⟩
    · show R.s0 < (R.s0+R.s1)/2
      linarith
    · show (R.s0+R.s1)/2 < R.s1
      linarith
    · rcases le_or_gt s (((R.s0+R.s1)/2 : ℚ) : ℝ) with h | h
      · left; exact ⟨m1, m2, m3, h⟩
      · right; exact ⟨m1, m2, h.le, m4⟩
