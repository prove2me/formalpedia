-- Prove2me | solution 1 for BellRegret.Paradoxes.ratio_strictMono_of_deriv2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:47:35.007226+00:00
-- url     : https://prove2.me/submissions/f4e0dbfa-b301-4b7c-a77c-16204c7646d2

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem strictMonoOn_div_aux (h : ℝ → ℝ) (h0 : h 0 = 0)
    (hc : StrictConvexOn ℝ (Set.Ici (0:ℝ)) h) :
    StrictMonoOn (fun x => h x / x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  simp only
  have ht : 0 < x / y := div_pos hx hy
  have ht1 : x / y < 1 := (div_lt_one hy).2 hxy
  have key := hc.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) (ne_of_lt hy)
    (show 0 < 1 - x / y by linarith) ht (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h0] at key
  have e : x / y * y = x := div_mul_cancel₀ x hy.ne'
  rw [e] at key
  rw [div_lt_div_iff₀ hx hy]
  calc h x * y < (x / y * h y) * y := mul_lt_mul_of_pos_right (by linarith) hy
    _ = h y * x := by field_simp

theorem solution (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (h2 : ∀ x : ℝ, 0 < x → deriv (deriv f) (-x) < deriv (deriv f) x) :
    StrictMonoOn (fun x => (f x - f (-x)) / x) (Set.Ioi 0) := by
  set h : ℝ → ℝ := fun x => f x - f (-x) with hh
  have hd : ∀ x, HasDerivAt h (deriv f x + deriv f (-x)) x := by
    intro x
    have h1 := (hf x).hasDerivAt
    have h3 := ((hf (-x)).hasDerivAt).comp x (hasDerivAt_neg x)
    have := h1.sub h3
    have e : h = f - f ∘ Neg.neg := by funext y; simp [hh]
    rw [e]
    exact this.congr_deriv (by ring)
  have hd' : deriv h = fun x => deriv f x + deriv f (-x) := funext fun x => (hd x).deriv
  have hdd : ∀ x, HasDerivAt (deriv h) (deriv (deriv f) x - deriv (deriv f) (-x)) x := by
    intro x
    rw [hd']
    have h1 := (hf' x).hasDerivAt
    have h3 := ((hf' (-x)).hasDerivAt).comp x (hasDerivAt_neg x)
    have := h1.add h3
    have e : (fun x => deriv f x + deriv f (-x)) = deriv f + deriv f ∘ Neg.neg := by
      funext y; simp
    rw [e]
    exact this.congr_deriv (by ring)
  have hcont : ContinuousOn h (Set.Ici 0) :=
    fun x _ => (hd x).continuousAt.continuousWithinAt
  have hconv : StrictConvexOn ℝ (Set.Ici (0:ℝ)) h := by
    apply strictConvexOn_of_deriv2_pos (convex_Ici 0) hcont
    intro x hx
    rw [interior_Ici] at hx
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [(hdd x).deriv]
    linarith [h2 x hx]
  exact strictMonoOn_div_aux h (by simp [hh]) hconv
