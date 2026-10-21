-- Prove2me | solution 1 for BellRegret.Paradoxes.negExp_conditions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:47:37.102782+00:00
-- url     : https://prove2.me/submissions/e20687d6-6299-4928-8a27-aa60e22cba40

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem negExp_hasDeriv (γ r : ℝ) :
    HasDerivAt (negExp γ) (γ * Real.exp (-(γ * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => -(γ * r)) (-γ) r := by
    exact (((hasDerivAt_id' r).const_mul γ).neg).congr_deriv (by ring)
  have h2 := (h1.exp).const_sub 1
  have e : negExp γ = fun r => 1 - Real.exp (-(γ * r)) := by funext y; rfl
  rw [e]
  exact h2.congr_deriv (by ring)

theorem deriv_negExp (γ : ℝ) : deriv (negExp γ) = fun r => γ * Real.exp (-(γ * r)) :=
  funext fun r => (negExp_hasDeriv γ r).deriv

theorem negExp_hasDeriv2 (γ r : ℝ) :
    HasDerivAt (fun r => γ * Real.exp (-(γ * r))) (-(γ * γ * Real.exp (-(γ * r)))) r := by
  have h1 : HasDerivAt (fun r : ℝ => -(γ * r)) (-γ) r := by
    exact (((hasDerivAt_id' r).const_mul γ).neg).congr_deriv (by ring)
  have h2 := h1.exp.const_mul γ
  exact h2.congr_deriv (by ring)

theorem deriv2_negExp (γ : ℝ) :
    deriv (deriv (negExp γ)) = fun r => -(γ * γ * Real.exp (-(γ * r))) := by
  rw [deriv_negExp]
  exact funext fun r => (negExp_hasDeriv2 γ r).deriv

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

theorem solution (γ : ℝ) (hγ : 0 < γ) :
    ConcaveOn ℝ Set.univ (negExp γ) ∧
    ConvexOn ℝ (Set.Ici 0) (regretG (negExp γ)) ∧
    StrictMonoOn (fun r => regretG (negExp γ) r / r) (Set.Ioi 0) := by
  have hγ2 : 0 < γ * γ := mul_pos hγ hγ
  -- explicit form of g
  set G : ℝ → ℝ := fun r => r + Real.exp (γ * r) - Real.exp (-(γ * r)) with hGdef
  have hG : regretG (negExp γ) = G := by
    funext r
    have e : -(γ * -r) = γ * r := by ring
    simp only [regretG, negExp, hGdef, e]
    ring
  have hlin : ∀ r : ℝ, HasDerivAt (fun r : ℝ => γ * r) γ r := fun r =>
    ((hasDerivAt_id' r).const_mul γ).congr_deriv (by ring)
  have hlin' : ∀ r : ℝ, HasDerivAt (fun r : ℝ => -(γ * r)) (-γ) r := fun r =>
    ((hlin r).neg)
  have hG1 : ∀ r, HasDerivAt G (1 + γ * Real.exp (γ * r) + γ * Real.exp (-(γ * r))) r := by
    intro r
    have h1 := ((hasDerivAt_id' r).add (hlin r).exp).sub (hlin' r).exp
    exact h1.congr_deriv (by ring)
  have hG2 : ∀ r, HasDerivAt (fun r => 1 + γ * Real.exp (γ * r) + γ * Real.exp (-(γ * r)))
      (γ * γ * Real.exp (γ * r) - γ * γ * Real.exp (-(γ * r))) r := by
    intro r
    have h1 := ((hasDerivAt_const r (1:ℝ)).add ((hlin r).exp.const_mul γ)).add
      ((hlin' r).exp.const_mul γ)
    exact h1.congr_deriv (by ring)
  have hdG : deriv G = fun r => 1 + γ * Real.exp (γ * r) + γ * Real.exp (-(γ * r)) :=
    funext fun r => (hG1 r).deriv
  have hddG : ∀ x, deriv (deriv G) x = γ * γ * Real.exp (γ * x) - γ * γ * Real.exp (-(γ * x)) := by
    intro x
    rw [hdG]
    exact (hG2 x).deriv
  have hconv : StrictConvexOn ℝ (Set.Ici (0:ℝ)) G := by
    apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    · exact fun x _ => (hG1 x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      simp only [Set.mem_Ioi] at hx
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
      rw [hddG]
      have : Real.exp (-(γ * x)) < Real.exp (γ * x) := Real.exp_lt_exp.2 (by nlinarith)
      nlinarith
  refine ⟨?_, ?_, ?_⟩
  · apply concaveOn_of_deriv2_nonpos convex_univ
    · exact fun x _ => (negExp_hasDeriv γ x).continuousAt.continuousWithinAt
    · exact fun x _ => (negExp_hasDeriv γ x).differentiableAt.differentiableWithinAt
    · rw [deriv_negExp]
      exact fun x _ => (negExp_hasDeriv2 γ x).differentiableAt.differentiableWithinAt
    · intro x _
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
      rw [deriv2_negExp]
      have := Real.exp_pos (-(γ * x))
      nlinarith
  · rw [hG]; exact hconv.convexOn
  · rw [hG]
    exact strictMonoOn_div_aux G (by simp [hGdef]) hconv
