-- Prove2me | solution 1 for BurauFaithful.sl2_euclid_step
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T05:56:30.548703+00:00
-- url     : https://prove2.me/submissions/55074baf-d3f3-444c-a9cd-444784eab9b6

/-
`BurauFaithful.sl2_euclid_step`: the Euclidean *descent* for `SL(2,ℤ)`, the engine of the
continued-fraction normal form `M = ±S^{ε} T^{a₁} S T^{a₂} ⋯`.

Right multiplication by `T^n` adds `n` times the first column to the second column
(`BurauFaithful.modular_T_zpow_mul`), and right multiplication by `S = !![0,-1;1,0]` swaps the two
columns with a sign. Hence, with the Euclidean quotient `n = -(M 0 1 / M 0 0)` (so that the
`(0,0)`-entry of `M * T^n` becomes the remainder `M 0 1 % M 0 0` of `M 0 1` modulo `M 0 0`), the
matrix
  `N = (M * T^n) * S`
has its `(0,0)`-entry equal to `M 0 1 % M 0 0`, of strictly smaller absolute value than `M 0 0`.
The measure `|M 0 0|` therefore decreases at every step of the Euclidean algorithm, which
terminates when `M 0 0 = 0` (and then `M = ±T^k`).

This is the decrease used in Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math.
Studies 82, §3.3, pp. 129-130, and is the same descent as `FixedDetMatrices.reduce` in Mathlib.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem solution (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M 0 0 ≠ 0) :
    ((M * (↑(ModularGroup.T ^ (-(M 0 1 / M 0 0))) : Matrix (Fin 2) (Fin 2) ℤ)) *
        (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = M 0 1 % M 0 0 ∧
      |((M * (↑(ModularGroup.T ^ (-(M 0 1 / M 0 0))) : Matrix (Fin 2) (Fin 2) ℤ)) *
        (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)) 0 0| < |M 0 0| := by
  have hkey : ((M * (↑(ModularGroup.T ^ (-(M 0 1 / M 0 0))) : Matrix (Fin 2) (Fin 2) ℤ)) *
        (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = M 0 1 % M 0 0 := by
    rw [ModularGroup.coe_T_zpow, ModularGroup.coe_S]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Int.emod_def]
    ring
  exact ⟨hkey, by
    rw [hkey]
    exact (abs_of_nonneg (Int.emod_nonneg (M 0 1) h)).trans_lt (Int.emod_lt_abs (M 0 1) h)⟩
