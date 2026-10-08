-- Prove2me | solution 1 for CosmoConstCentury.de_sitter_solution_B_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:15:08.946988+00:00
-- url     : https://prove2.me/submissions/896da4c0-260b-48a0-b71d-ae4f36697aeb

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace A59b0c0bAux

lemma deriv_R (c R₀ : ℝ) (hR₀ : 0 < R₀) :
    deriv (fun t => R₀ * Real.cosh (c * t / R₀)) = fun t => c * Real.sinh (c * t / R₀) := by
  funext t
  have h1 : HasDerivAt (fun t => c * t / R₀) (c / R₀) t := by
    have := ((hasDerivAt_id t).const_mul c).div_const R₀
    simpa using this
  have h2 := (h1.cosh).const_mul R₀
  rw [h2.deriv]
  field_simp

lemma deriv2_R (c R₀ : ℝ) (hR₀ : 0 < R₀) :
    deriv (fun t => c * Real.sinh (c * t / R₀)) = fun t => c * c / R₀ * Real.cosh (c * t / R₀) := by
  funext t
  have h1 : HasDerivAt (fun t => c * t / R₀) (c / R₀) t := by
    have := ((hasDerivAt_id t).const_mul c).div_const R₀
    simpa using this
  have h2 := (h1.sinh).const_mul c
  rw [h2.deriv]
  ring

end A59b0c0bAux

open CosmoConstCentury in
theorem solution (G c Λ R₀ : ℝ) (hR₀ : 0 < R₀) :
    IsFriedmannSolution G c Λ 1 Set.univ (fun t => R₀ * Real.cosh (c * t / R₀)) (fun _ => 0) ↔
      Λ = 3 * c ^ 2 / R₀ ^ 2 := by
  unfold IsFriedmannSolution
  rw [A59b0c0bAux.deriv_R c R₀ hR₀, A59b0c0bAux.deriv2_R c R₀ hR₀]
  have key : ∀ t : ℝ, Real.cosh (c * t / R₀) ^ 2 = Real.sinh (c * t / R₀) ^ 2 + 1 := by
    intro t; have := Real.cosh_sq_sub_sinh_sq (c * t / R₀); linarith
  constructor
  · intro h
    obtain ⟨_, _, h1, _⟩ := h 0 (Set.mem_univ _)
    simp only [mul_zero, zero_div, Real.cosh_zero, Real.sinh_zero] at h1
    have : Λ = 3 * c ^ 2 / R₀ ^ 2 := by
      field_simp at h1 ⊢
      linarith
    exact this
  · intro hΛ t _
    have hc : 0 < Real.cosh (c * t / R₀) := Real.cosh_pos _
    refine ⟨mul_pos hR₀ hc, ?_, ?_, ?_⟩
    · fun_prop
    · subst hΛ
      simp only [mul_zero]
      field_simp
      rw [key t]; ring
    · subst hΛ
      field_simp
      rw [key t]; ring
