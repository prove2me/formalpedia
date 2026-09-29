-- Prove2me | solution 1 for Chou.not_hasExponentialGrowth_of_isExponentiallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-21T16:29:49.352492+00:00
-- url     : https://prove2.me/submissions/4b231476-017f-4f4f-9bf5-5732acacc182

import Definitions.Def_Chou_Growth
import Theorems.Thm_Chou_hasExponentialGrowth_iff_forall
import Mathlib

set_option autoImplicit false

open Chou

/-- Child 1 of Chou.milnor_wolf: exponential boundedness precludes exponential growth.
    Uses the proved generating-set invariance `hasExponentialGrowth_iff_forall` to force
    both witnesses onto the same generating set, then diagonalises with c' = (1+c)/2. -/
theorem solution {G : Type*} [Group G] [Group.FG G]
    (h : IsExponentiallyBounded G) : ¬ HasExponentialGrowth G := by
  intro hexp
  rw [hasExponentialGrowth_iff_forall] at hexp
  obtain ⟨S, hSgen, hbound⟩ := h
  obtain ⟨c, hc1, hclower⟩ := hexp S hSgen
  set c' : ℝ := (1 + c) / 2 with hc'def
  have h1c' : (1 : ℝ) < c' := by rw [hc'def]; linarith
  have hc'c : c' < c := by rw [hc'def]; linarith
  obtain ⟨N, hN⟩ := hbound c' h1c'
  have hle := hN (N + 1) (Nat.le_succ N)
  have hge := hclower (N + 1)
  have hlt : c' ^ (N + 1) < c ^ (N + 1) :=
    pow_lt_pow_left₀ hc'c (by linarith) (Nat.succ_ne_zero N)
  have hcard : (Nat.card (wordBall (S : Set G) (N + 1)) : ℝ) =
      (Nat.card (wordBall (S : Set G) (N + 1)) : ℝ) := rfl
  linarith
