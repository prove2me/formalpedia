-- Prove2me | solution 1 for CelestialWedge.wedge_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:53:06.842644+00:00
-- url     : https://prove2.me/submissions/bae31e4c-46db-49a6-b675-e1799157201a

import Mathlib
import Definitions.Def_celestial_wedge_algebra

open CelestialWedge in
theorem solution (p m q n : ℚ) (hpm : InWedge p m) (hqn : InWedge q n)
    (hc : structConst p m q n ≠ 0) : InWedge (p + q - 2) (m + n) := by
  obtain ⟨a, b, ha, hb⟩ := hpm
  obtain ⟨c, d, hc', hd⟩ := hqn
  unfold structConst at hc
  have h1 : 1 ≤ a + c := by
    by_contra h
    have ha0 : a = 0 := by omega
    have hc0 : c = 0 := by omega
    subst ha0 hc0
    apply hc
    have e1 : m = 1 - p := by push_cast at ha; linarith
    have e2 : n = 1 - q := by push_cast at hc'; linarith
    subst e1 e2
    ring
  have h2 : 1 ≤ b + d := by
    by_contra h
    have hb0 : b = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hb0 hd0
    apply hc
    have e1 : m = p - 1 := by push_cast at hb; linarith
    have e2 : n = q - 1 := by push_cast at hd; linarith
    subst e1 e2
    ring
  refine ⟨a + c - 1, b + d - 1, ?_, ?_⟩
  · rw [Nat.cast_sub h1]; push_cast; linarith
  · rw [Nat.cast_sub h2]; push_cast; linarith
