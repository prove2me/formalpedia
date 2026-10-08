-- Prove2me | solution 1 for ContactCalculus.lie_derivative_eq_exterior_of_annihilation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T18:48:43.662541+00:00
-- url     : https://prove2.me/submissions/b3a9d13c-9039-4949-9c4f-2f75c13cef9e

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Linarith

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : V → (V →L[ℝ] ℝ)) (X : V → V)
    (hη : Differentiable ℝ η) (hX : Differentiable ℝ X)
    (hz : ∀ y, η y (X y) = 0) (y v : V) :
    fderiv ℝ η y (X y) v + η y (fderiv ℝ X y v) =
      fderiv ℝ η y (X y) v - fderiv ℝ η y v (X y) := by
  have hd := (hη y).hasFDerivAt.clm_apply (hX y).hasFDerivAt
  have hfun : (fun z => η z (X z)) = (fun _ : V => (0 : ℝ)) := funext hz
  have hf : fderiv ℝ (fun z => η z (X z)) y = 0 := by
    rw [hfun]
    simpa using congrArg (fun L : V → V →L[ℝ] ℝ => L y)
      (fderiv_const (𝕜 := ℝ) (E := V) (0 : ℝ))
  have he := congrArg (fun L : V →L[ℝ] ℝ => L v) hd.fderiv
  rw [hf] at he
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply] at he
  linarith
