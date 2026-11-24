-- Prove2me | solution 1 for FourBlockIP350.Main.affine_subtraction
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:53:21.677465+00:00
-- url     : https://prove2.me/submissions/6e94fdcf-0e87-4ea5-bc5d-fdf9d53dbcc4

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

set_option autoImplicit false

open FourBlockIP350.Main

open scoped BigOperators

private lemma affine_mid {k : ℕ} (A : RVec k →ᵃ[ℝ] ℝ) (x y m : RVec k)
    (hxy : x + y = (2 : ℝ) • m) : A x + A y = 2 * A m := by
  have hx : A x = A.linear (x - m) + A m := by
    have := A.linearMap_vsub x m
    simp only [vsub_eq_sub] at this
    linarith
  have hy : A y = A.linear (y - m) + A m := by
    have := A.linearMap_vsub y m
    simp only [vsub_eq_sub] at this
    linarith
  have hsum : (x - m) + (y - m) = 0 := by
    rw [show (x - m) + (y - m) = (x + y) - (2 : ℝ) • m by rw [two_smul]; abel, hxy, sub_self]
  have hl : A.linear (x - m) + A.linear (y - m) = 0 := by
    rw [← map_add, hsum, map_zero]
  linarith

theorem solution {k : ℕ} (hk : 0 < k) (h : ZVec k → ℝ)
    (hh : MidpointConvex h) (A : RVec k →ᵃ[ℝ] ℝ) :
    MidpointConvex (fun v => h v - A (realVec v)) := by
  intro a b w hab
  have h1 := hh a b w hab
  have hr : realVec a + realVec b = (2 : ℝ) • realVec w := by
    funext j
    have := congrFun hab j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [realVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast this
  have h2 := affine_mid A _ _ _ hr
  simp only
  linarith
