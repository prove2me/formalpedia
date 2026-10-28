-- Prove2me | solution 1 for ContinuityEqWiki.electron_continuity_product_rule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:31.916242+00:00
-- url     : https://prove2.me/submissions/8b241e3a-3514-419a-9987-8c672cdba802

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

theorem solution (e μ D : ℝ) (he : 0 < e) (n E G R : ℝ → ℝ → ℝ)
    (hn : ∀ t, ContDiff ℝ 2 (n t)) (hE : ∀ t, Differentiable ℝ (E t))
    (conservation : ∀ t x, deriv (fun s => n s x) t =
      1 / e * deriv (fun y => e * n t y * μ * E t y + e * D * deriv (n t) y) x
        + (G t x - R t x)) :
    ∀ t x, deriv (fun s => n s x) t =
      μ * E t x * deriv (n t) x + μ * n t x * deriv (E t) x + D * deriv (deriv (n t)) x
        + (G t x - R t x) := by
  intro t x
  rw [conservation t x]
  have h2 : ContDiff ℝ 2 (n t) := hn t
  have hn1 : HasDerivAt (n t) (deriv (n t) x) x :=
    ((h2.differentiable (by norm_num)) x).hasDerivAt
  have hn2 : HasDerivAt (deriv (n t)) (deriv (deriv (n t)) x) x :=
    (h2.differentiable_deriv_two x).hasDerivAt
  have hE1 : HasDerivAt (E t) (deriv (E t) x) x := ((hE t) x).hasDerivAt
  have h := (((hn1.const_mul e).mul_const μ).mul hE1).add (hn2.const_mul (e * D))
  have h' : HasDerivAt (fun y => e * n t y * μ * E t y + e * D * deriv (n t) y)
      (e * deriv (n t) x * μ * E t x + e * n t x * μ * deriv (E t) x
        + e * D * deriv (deriv (n t)) x) x := by
    exact h
  rw [h'.deriv]
  field_simp
