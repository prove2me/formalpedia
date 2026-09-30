-- Prove2me | solution 1 for BurauFaithful.modular_T_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T05:44:02.696907+00:00
-- url     : https://prove2.me/submissions/b03d5268-1b36-418d-8a73-ff1915260a96

/-
`BurauFaithful.modular_T_zpow_mul`: the elementary step of the Euclidean algorithm for
`SL(2,ℤ)`, phrased for the classical generator `T = !![1,1;0,1]`: right multiplication by `T^n`
adds `n` times the first column to the second column.

This is the engine of the continued-fraction normal form `M = ±S^{ε}T^{a₁}ST^{a₂}…` used to prove
that the map `⟨s₁,s₂ | s₁s₂s₁ = s₂s₁s₂, (s₁s₂s₁)⁴ = 1⟩ → SL(2,ℤ)` is injective
(Coxeter–Moser; Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82,
§3.3, pp. 129–130).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem solution (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℤ) :
    M * (↑(ModularGroup.T ^ n) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![M 0 0, M 0 1 + n * M 0 0; M 1 0, M 1 1 + n * M 1 0] := by
  rw [ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
