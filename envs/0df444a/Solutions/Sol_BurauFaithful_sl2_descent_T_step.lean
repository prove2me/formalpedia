-- Prove2me | solution 1 for BurauFaithful.sl2_descent_T_step
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T07:04:01.527763+00:00
-- url     : https://prove2.me/submissions/b6685b6c-94bb-48d9-b4b4-b148dc76ce65

/-
`BurauFaithful.sl2_descent_T_step`: the arithmetic core of the **T-rule** for the Euclidean descent
section `ρ : SL(2,ℤ) → B₃/⟨Δ⁴⟩` (see `NOTES_BURAU.md`, SESSION 14).

The descent step attached to `M` with `M 0 0 ≠ 0` uses the Euclidean quotient
`n(M) = -(M 0 1 / M 0 0)` and the target `N = (M · T^{n(M)}) · S`.  Right multiplication by `T^j`
does not change `M 0 0` and adds `j · (M 0 0)` to `M 0 1`, so

    n(M · T^j) = n(M) - j ,        i.e.   -( (M T^j) 0 1 / (M T^j) 0 0 ) = -(M 0 1 / M 0 0) - j ,

and the descent target is *literally unchanged*:
`((M T^j) · T^{n(M)-j}) · S = (M · T^{n(M)}) · S`.  Hence
`ρ(M · T^j) = ρ(M) · (lift T)^j`, which is one of the two multiplication rules that make `ρ` a
section of the specialization `φ` and thereby prove `BurauFaithful.spec_reduced_kernel_le`.

This is the integer-arithmetic heart of `BurauFaithful.modular_T_zpow_mul` at the level of the
descent recursion.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem solution (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M 0 0 ≠ 0) (j : ℤ) :
    -(((M * (↑(ModularGroup.T ^ j) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1) /
        ((M * (↑(ModularGroup.T ^ j) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0)) =
      -(M 0 1 / M 0 0) - j := by
  rw [ModularGroup.coe_T_zpow]
  have h00 : (M * (!![1, j; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = M 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (M * (!![1, j; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 = M 0 1 + j * M 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h00, h01, mul_comm j (M 0 0), Int.add_mul_ediv_left (M 0 1) j h]
  ring
