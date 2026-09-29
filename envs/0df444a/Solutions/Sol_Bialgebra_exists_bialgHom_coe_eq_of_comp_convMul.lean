-- Prove2me | solution 1 for Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c6607e34-544a-5403-9228-d73b112601f8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

open Algebra.TensorProduct in

theorem L3b_conv_includeLeft_includeRight (R : Type u) [CommRing R] (C : Type u) [CommRing C] [Bialgebra R C] :
    (WithConv.toConv (includeLeft : C →ₐ[R] C ⊗[R] C) *
      WithConv.toConv (includeRight : C →ₐ[R] C ⊗[R] C)).ofConv = Bialgebra.comulAlgHom R C := by
  rw [AlgHom.convMul_def]
  show (lmul' R).comp ((map includeLeft includeRight).comp (Bialgebra.comulAlgHom R C)) = _
  have h : (lmul' R (S := C ⊗[R] C)).comp (map (includeLeft : C →ₐ[R] C ⊗[R] C) includeRight) =
      AlgHom.id R (C ⊗[R] C) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [tmul_mul_tmul]
  rw [← AlgHom.comp_assoc, h, AlgHom.id_comp]

open Algebra.TensorProduct in
theorem solution
    {R : Type u} [CommRing R] {H B : Type u} [CommRing H] [Bialgebra R H] [CommRing B] [Bialgebra R B]
    (ψ : H →ₐ[R] B)
    (hmul : ∀ (T : Type u) [CommRing T] [Algebra R T] (χ χ' : WithConv (B →ₐ[R] T)),
      WithConv.toConv ((χ * χ').ofConv.comp ψ) = WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ))
    (hone : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv.toConv ((1 : WithConv (B →ₐ[R] T)).ofConv.comp ψ) = (1 : WithConv (H →ₐ[R] T))) :
    ∃ ψ' : H →ₐc[R] B, (ψ' : H →ₐ[R] B) = ψ := by

  have hcounit : (Bialgebra.counitAlgHom R B).comp ψ = Bialgebra.counitAlgHom R H := by
    have h := congrArg WithConv.ofConv (hone R)
    simp only [WithConv.ofConv_toConv] at h
    rw [AlgHom.convOne_def, AlgHom.convOne_def] at h
    simp only [WithConv.ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp] at h
    exact h

  have hcomul : (map ψ ψ).comp (Bialgebra.comulAlgHom R H) = (Bialgebra.comulAlgHom R B).comp ψ := by
    have h := congrArg WithConv.ofConv
      (hmul (B ⊗[R] B) (WithConv.toConv includeLeft) (WithConv.toConv includeRight))
    simp only [WithConv.ofConv_toConv] at h
    rw [L3b_conv_includeLeft_includeRight R B] at h
    rw [h]

    have h2 := AlgHom.comp_convMul_distrib (map ψ ψ)
      (WithConv.toConv (includeLeft : H →ₐ[R] H ⊗[R] H)) (WithConv.toConv (includeRight : H →ₐ[R] H ⊗[R] H))
    rw [L3b_conv_includeLeft_includeRight R H] at h2
    rw [h2]
    simp only [WithConv.ofConv_toConv, map_comp_includeLeft, map_comp_includeRight]
  exact ⟨BialgHom.ofAlgHom ψ hcounit hcomul, rfl⟩

end S_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul
end P2MW
export P2MW.S_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul (solution)
