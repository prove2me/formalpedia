-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_log_concave_of_scale_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:32:51.416468+00:00
-- url     : https://prove2.me/submissions/d7ab3f97-528c-4aab-b6a8-ebec0b30eb33

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (φ : ℝ) (W V : ℝ → ℝ)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hWconcave : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (W x))) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by
  have hlinear : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x : ℝ => -(φ * x)) := by
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp
    convert le_refl (-(φ * (a * x + b * y))) using 1 <;> ring
  have hsum : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x : ℝ => Real.log (W x) + -(φ * x)) := by
    convert hWconcave.add hlinear using 1 <;> rfl
  apply hsum.congr
  intro x hx
  change Real.log (W x) + -(φ * x) = Real.log (V x)
  have hw : W x ≠ 0 := ne_of_gt (hWpos x hx)
  rw [hV x hx, Real.log_mul (Real.exp_ne_zero _) hw, Real.log_exp]
  ring
