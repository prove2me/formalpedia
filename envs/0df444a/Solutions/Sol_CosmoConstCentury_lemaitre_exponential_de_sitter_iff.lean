-- Prove2me | solution 1 for CosmoConstCentury.lemaitre_exponential_de_sitter_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:29:14.139354+00:00
-- url     : https://prove2.me/submissions/8a449e0b-2c52-456e-a93b-aef1cdacf492

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

set_option autoImplicit false

open Filter Topology

namespace CosmoConstCentury446

lemma deriv_expmul (a : ℝ) : deriv (fun t : ℝ => Real.exp (a * t)) = fun t => a * Real.exp (a * t) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => Real.exp (a * t)) (Real.exp (a * t) * (a * 1)) t :=
    ((hasDerivAt_id t).const_mul a).exp
  rw [h.deriv]; ring

lemma deriv2_expmul (a : ℝ) : deriv (deriv (fun t : ℝ => Real.exp (a * t))) = fun t => a ^ 2 * Real.exp (a * t) := by
  rw [deriv_expmul]
  funext t
  have h : HasDerivAt (fun t : ℝ => a * Real.exp (a * t)) (a * (Real.exp (a * t) * (a * 1))) t :=
    (((hasDerivAt_id t).const_mul a).exp).const_mul a
  rw [h.deriv]; ring

end CosmoConstCentury446

open Filter Topology in
open CosmoConstCentury in
theorem solution (G c Λ a : ℝ) :
    IsFriedmannSolution G c Λ 0 Set.univ (fun t => Real.exp (a * t)) (fun _ => 0) ↔
      Λ = 3 * a ^ 2 := by
  unfold CosmoConstCentury.IsFriedmannSolution
  rw [CosmoConstCentury446.deriv2_expmul, CosmoConstCentury446.deriv_expmul]
  constructor
  · intro h
    obtain ⟨_, _, h1, _⟩ := h 0 trivial
    have he : Real.exp (a * 0) ≠ 0 := (Real.exp_pos _).ne'
    field_simp at h1
    simp at h1
    linarith
  · intro hΛ t _
    have he : Real.exp (a * t) ≠ 0 := (Real.exp_pos _).ne'
    refine ⟨Real.exp_pos _, ?_, ?_, ?_⟩
    · fun_prop
    · field_simp; simp; subst hΛ; ring
    · field_simp; subst hΛ; ring
