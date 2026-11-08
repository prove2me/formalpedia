-- Prove2me | solution 1 for EllipsoidFitting.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:08:45.832162+00:00
-- url     : https://prove2.me/submissions/f991ee93-72fe-4009-823d-ab759809b275

import Mathlib
import Definitions.Def_EllipsoidFitting_Fits
import Definitions.Def_EllipsoidFitting_perturbR

set_option autoImplicit false

open Matrix
open scoped MatrixOrder

namespace EllipsoidFitting.Aux_EF32

theorem trace_vecMulVec_mul {d : ℕ} (u : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℝ) :
    (vecMulVec u u * Y).trace = u ⬝ᵥ (Y *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end EllipsoidFitting.Aux_EF32

open EllipsoidFitting EllipsoidFitting.Aux_EF32 in
theorem solution {m d : ℕ} (v : Fin m → Fin d → ℝ) (hM : IsUnit (gram v).det)
    (Λ : Matrix (Fin d) (Fin d) ℝ) (hΛ : Λ.PosSemidef) (hS : Λ ∈ imageS v)
    (htr : (Λ * (1 - perturbR v)).trace < 0) : ¬ Fits v := by
  rintro ⟨X, hX, hXc⟩
  set R := perturbR v with hRdef
  -- the perturbation reproduces `eta` on the constraints
  have hR : ∀ i, v i ⬝ᵥ (R *ᵥ v i) = eta v i := by
    intro i
    set c := (gram v)⁻¹ *ᵥ eta v with hc
    have hterm : ∀ t, v i ⬝ᵥ ((c t • vecMulVec (v t) (v t)) *ᵥ v i) = gram v i t * c t := by
      intro t
      rw [Matrix.smul_mulVec, vecMulVec_mulVec, dotProduct_smul, dotProduct_smul]
      simp only [EllipsoidFitting.gram, Matrix.of_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      rw [dotProduct_comm (v t) (v i)]
      ring
    rw [hRdef, perturbR, liftMap, Matrix.sum_mulVec, dotProduct_sum]
    simp only [← hc, hterm]
    have : (EllipsoidFitting.gram v *ᵥ c) i = eta v i := by
      rw [hc, mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]
    rw [← this]
    rfl
  -- the difference `X - (1 - R)` vanishes on the constraints
  set Y := X - (1 - R) with hY
  have hYc : ∀ i, v i ⬝ᵥ (Y *ᵥ v i) = 0 := by
    intro i
    rw [hY, sub_mulVec, sub_mulVec, one_mulVec, dotProduct_sub, dotProduct_sub, hXc i, hR i]
    simp only [eta, constraintMap, one_mulVec]
    ring
  -- hence `Λ` is orthogonal to `Y`
  have hΛY' : ∀ Λ' ∈ imageS v, (Λ' * Y).trace = 0 := by
    intro Λ' hΛ'
    induction hΛ' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [trace_vecMulVec_mul]
      exact hYc t
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hΛY : (Λ * Y).trace = 0 := hΛY' Λ hS
  -- trace of a product of PSD matrices is nonnegative
  have htrnn : 0 ≤ (Λ * X).trace := by
    have hX0 : 0 ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
    set Sq := CFC.sqrt X with hSqdef
    have hSq : Sq * Sq = X := CFC.sqrt_mul_sqrt_self X hX0
    have hSqsa : Sqᴴ = Sq := (CFC.sqrt_nonneg X).isSelfAdjoint
    have h := (hΛ.conjTranspose_mul_mul_same Sq).trace_nonneg
    rw [hSqsa] at h
    rw [← hSq, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    exact h
  have hsplit : 1 - R = X - Y := by rw [hY]; abel
  rw [hsplit, Matrix.mul_sub, Matrix.trace_sub, hΛY, sub_zero] at htr
  linarith
