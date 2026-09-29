-- Prove2me | solution 1 for BialgHom.exists_comp_eq_of_natural_of_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/04f134b2-9ca4-5ef5-a3d5-2c4a5b113717

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_BialgHom_exists_comp_eq_of_natural_of_map_mul

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open WithConv

universe u v

namespace BialgHom
p2m_export "BialgHom" "comp_assoc convOne_def comp_id ext id_comp convMul_def ofAlgHom comp"
namespace YonedaMonoidal
p2m_open "BialgHom"

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]

theorem ofConv_includeLeft_mul_includeRight :
    (toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
      toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)).ofConv =
      Bialgebra.comulAlgHom R H := by
  rw [AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv]
  have key : (Algebra.TensorProduct.lmul' R (S := H ⊗[R] H)).comp
      (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
        (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) = AlgHom.id R (H ⊗[R] H) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [← AlgHom.comp_assoc, key, AlgHom.id_comp]

theorem ofConv_toConv_comp_mul_toConv_comp {H' : Type v} [CommRing H'] [Bialgebra R H']
    {T : Type v} [CommRing T] [Algebra R T] (f g : H →ₐ[R] T) (r : H' →ₐ[R] H) :
    (toConv (f.comp r) * toConv (g.comp r)).ofConv =
      ((Algebra.TensorProduct.lmul' R (S := T)).comp (Algebra.TensorProduct.map f g)).comp
        ((Algebra.TensorProduct.map r r).comp (Bialgebra.comulAlgHom R H')) := by
  rw [AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv, Algebra.TensorProduct.map_comp]
  simp only [AlgHom.comp_assoc]

end BialgHom.YonedaMonoidal

open BialgHom.YonedaMonoidal in
theorem solution
    {R : Type u} [CommRing R] {H₁ H₂ : Type v} [CommRing H₁] [Bialgebra R H₁] [CommRing H₂] [Bialgebra R H₂]
    (η : ∀ (T : Type v) [CommRing T] [Algebra R T], WithConv (H₁ →ₐ[R] T) → WithConv (H₂ →ₐ[R] T))
    (hη : ∀ (T T' : Type v) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T')
      (φ : WithConv (H₁ →ₐ[R] T)),
      WithConv.ofConv (η T' (WithConv.toConv (g.comp (WithConv.ofConv φ)))) = g.comp (WithConv.ofConv (η T φ)))
    (hmul : ∀ (T : Type v) [CommRing T] [Algebra R T] (φ ψ : WithConv (H₁ →ₐ[R] T)), η T (φ * ψ) = η T φ * η T ψ)
    (hone : ∀ (T : Type v) [CommRing T] [Algebra R T], η T 1 = 1) :
    ∃ r : H₂ →ₐc[R] H₁, ∀ (T : Type v) [CommRing T] [Algebra R T] (φ : WithConv (H₁ →ₐ[R] T)),
      WithConv.ofConv (η T φ) = (WithConv.ofConv φ).comp (r : H₂ →ₐ[R] H₁) := by
  classical

  let r₀ : H₂ →ₐ[R] H₁ := (η H₁ (toConv (AlgHom.id R H₁))).ofConv
  have hchar : ∀ (T : Type v) [CommRing T] [Algebra R T] (φ : WithConv (H₁ →ₐ[R] T)),
      (η T φ).ofConv = φ.ofConv.comp r₀ := by
    intro T _ _ φ
    have h := hη H₁ T φ.ofConv (toConv (AlgHom.id R H₁))
    rw [ofConv_toConv, AlgHom.comp_id, toConv_ofConv] at h
    exact h

  have hcounit : (Bialgebra.counitAlgHom R H₁).comp r₀ = Bialgebra.counitAlgHom R H₂ := by
    have h1 := congrArg WithConv.ofConv (hone H₁)
    rw [hchar H₁ 1, AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ofConv_toConv,
      AlgHom.comp_assoc] at h1
    have h2 := congrArg (fun f : H₂ →ₐ[R] H₁ => (Bialgebra.counitAlgHom R H₁).comp f) h1
    simp only [← AlgHom.comp_assoc] at h2
    have hret : (Bialgebra.counitAlgHom R H₁).comp (Algebra.ofId R H₁) = AlgHom.id R R := by
      ext
    rw [hret, AlgHom.id_comp, AlgHom.id_comp] at h2
    exact h2

  have hcomul : (Algebra.TensorProduct.map r₀ r₀).comp (Bialgebra.comulAlgHom R H₂) =
      (Bialgebra.comulAlgHom R H₁).comp r₀ := by
    have h1 := congrArg WithConv.ofConv (hmul (H₁ ⊗[R] H₁)
      (toConv (Algebra.TensorProduct.includeLeft : H₁ →ₐ[R] H₁ ⊗[R] H₁))
      (toConv (Algebra.TensorProduct.includeRight : H₁ →ₐ[R] H₁ ⊗[R] H₁)))
    rw [hchar, ofConv_includeLeft_mul_includeRight] at h1
    have h2 : η (H₁ ⊗[R] H₁) (toConv (Algebra.TensorProduct.includeLeft : H₁ →ₐ[R] H₁ ⊗[R] H₁)) =
        toConv ((Algebra.TensorProduct.includeLeft : H₁ →ₐ[R] H₁ ⊗[R] H₁).comp r₀) := by
      rw [← toConv_ofConv (η _ _), hchar, ofConv_toConv]
    have h3 : η (H₁ ⊗[R] H₁) (toConv (Algebra.TensorProduct.includeRight : H₁ →ₐ[R] H₁ ⊗[R] H₁)) =
        toConv ((Algebra.TensorProduct.includeRight : H₁ →ₐ[R] H₁ ⊗[R] H₁).comp r₀) := by
      rw [← toConv_ofConv (η _ _), hchar, ofConv_toConv]
    rw [h2, h3, ofConv_toConv_comp_mul_toConv_comp] at h1
    have key : (Algebra.TensorProduct.lmul' R (S := H₁ ⊗[R] H₁)).comp
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : H₁ →ₐ[R] H₁ ⊗[R] H₁)
          (Algebra.TensorProduct.includeRight : H₁ →ₐ[R] H₁ ⊗[R] H₁)) = AlgHom.id R (H₁ ⊗[R] H₁) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [key, AlgHom.id_comp] at h1
    exact h1.symm
  refine ⟨BialgHom.ofAlgHom r₀ hcounit hcomul, fun T _ _ φ => ?_⟩
  rw [hchar]
  rfl

end S_BialgHom_exists_comp_eq_of_natural_of_map_mul
end P2MW
export P2MW.S_BialgHom_exists_comp_eq_of_natural_of_map_mul (solution)
