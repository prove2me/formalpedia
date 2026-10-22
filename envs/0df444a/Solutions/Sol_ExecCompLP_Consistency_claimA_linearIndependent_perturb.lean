-- Prove2me | solution 1 for ExecCompLP.Consistency.claimA_linearIndependent_perturb
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:29:47.270335+00:00
-- url     : https://prove2.me/submissions/2d25c0d2-7e9d-44ce-9d66-a82eb23550cb

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.FunProp

set_option autoImplicit false
open scoped Matrix.Norms.Elementwise

theorem solution {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) (hS : LinearIndependent ℝ (fun j : S => fun i => ξ i j)) :
    ∃ δ > 0, ∀ X : Matrix (Fin m) (Fin n) ℝ, (∀ i j, |X i j - ξ i j| < δ) →
      LinearIndependent ℝ (fun j : S => fun i => X i j) := by
  have hc : Continuous (fun X : Matrix (Fin m) (Fin n) ℝ =>
      fun j : S => fun i => X i j) := by fun_prop
  have ho : IsOpen {X : Matrix (Fin m) (Fin n) ℝ |
      LinearIndependent ℝ (fun j : S => fun i => X i j)} :=
    isOpen_setOfPred_linearIndependent.preimage hc
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho ξ hS
  refine ⟨δ, hδ, fun X hX => hball ?_⟩
  change dist X ξ < δ
  rw [dist_eq_norm, Matrix.norm_def]
  apply (pi_norm_lt_iff hδ).mpr
  intro i
  apply (pi_norm_lt_iff hδ).mpr
  intro j
  simpa only [Pi.sub_apply, Matrix.sub_apply, Real.norm_eq_abs] using hX i j

#print axioms solution
