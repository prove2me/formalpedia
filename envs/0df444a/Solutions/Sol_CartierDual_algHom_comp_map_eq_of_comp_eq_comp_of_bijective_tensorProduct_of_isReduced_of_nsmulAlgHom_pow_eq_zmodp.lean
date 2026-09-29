-- Prove2me | solution 1 for CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/207e1532-649a-5ee8-b5e9-b02c1725d50a

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic

import Theorems.Thm_CartierDual_algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp

set_option autoImplicit false

open scoped TensorProduct

namespace Ws50R3

variable {R : Type} [CommRing R]
variable {B : Type} [CommRing B] [HopfAlgebra R B] [Coalgebra.IsCocomm R B] [Module.Finite R B] [Module.Free R B]
variable {Gc : Type} [CommRing Gc] [HopfAlgebra R Gc] [Coalgebra.IsCocomm R Gc] [Module.Finite R Gc] [Module.Free R Gc]
variable {Ge : Type} [CommRing Ge] [HopfAlgebra R Ge] [Coalgebra.IsCocomm R Ge] [Module.Finite R Ge] [Module.Free R Ge]

theorem dualDistrib_comp_tmul (f : Module.Dual R Gc) (g : Module.Dual R Ge) (u : B →ₗ[R] Gc) (v : B →ₗ[R] Ge)
    (x : B ⊗[R] B) :
    TensorProduct.dualDistrib R B B ((f ∘ₗ u) ⊗ₜ[R] (g ∘ₗ v)) x =
      TensorProduct.dualDistrib R Gc Ge (f ⊗ₜ[R] g) (TensorProduct.map u v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.dualDistrib_apply]
  | add x y hx hy => simp [map_add, hx, hy]

noncomputable def Lam (qc : B →ₐc[R] Gc) (πe : B →ₐc[R] Ge) :
    CartierDual R Gc ⊗[R] CartierDual R Ge →ₐ[R] CartierDual R B :=
  Algebra.TensorProduct.productMap (CartierDual.mapAlgHom qc) (CartierDual.mapAlgHom πe)

theorem Lam_tmul (qc : B →ₐc[R] Gc) (πe : B →ₐc[R] Ge) (φ : CartierDual R Gc) (ψ : CartierDual R Ge) :
    Lam qc πe (φ ⊗ₜ[R] ψ) = CartierDual.mapAlgHom qc φ * CartierDual.mapAlgHom πe ψ :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

theorem Lam_apply (qc : B →ₐc[R] Gc) (πe : B →ₐc[R] Ge) (Θ : B →ₐc[R] Gc ⊗[R] Ge)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[R] Gc) (πe : B →ₐ[R] Ge) (Coalgebra.comul (R := R) b))
    (w : CartierDual R Gc ⊗[R] CartierDual R Ge) (b : B) :
    Lam qc πe w b = TensorProduct.dualDistrib R Gc Ge w (Θ b) := by

  have hlin : (LinearMap.applyₗ (R := R) b).comp ((CartierDual.toDual R B).toLinearMap.comp (Lam qc πe).toLinearMap) =
      (LinearMap.applyₗ (R := R) (Θ b)).comp (TensorProduct.dualDistrib R Gc Ge) := by
    refine TensorProduct.ext' fun φ ψ => ?_
    show CartierDual.toDual R B (Lam qc πe (φ ⊗ₜ[R] ψ)) b = TensorProduct.dualDistrib R Gc Ge (φ ⊗ₜ[R] ψ) (Θ b)
    rw [CartierDual.toDual_apply, Lam_tmul, CartierDual.mul_apply, hΘΔ]
    have h1 : CartierDual.toDual R B (CartierDual.mapAlgHom qc φ) = (CartierDual.toDual R Gc φ) ∘ₗ (qc : B →ₐ[R] Gc).toLinearMap := by
      ext a; rfl
    have h2 : CartierDual.toDual R B (CartierDual.mapAlgHom πe ψ) = (CartierDual.toDual R Ge ψ) ∘ₗ (πe : B →ₐ[R] Ge).toLinearMap := by
      ext a; rfl
    rw [h1, h2, dualDistrib_comp_tmul]
    rfl
  have := congrArg (fun (L : CartierDual R Gc ⊗[R] CartierDual R Ge →ₗ[R] R) => L w) hlin
  exact this

theorem Lam_surjective (qc : B →ₐc[R] Gc) (πe : B →ₐc[R] Ge) (Θ : B →ₐc[R] Gc ⊗[R] Ge) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[R] Gc) (πe : B →ₐ[R] Ge) (Coalgebra.comul (R := R) b)) :
    Function.Surjective (Lam qc πe) := by
  intro θ
  let eΘ : B ≃ₗ[R] Gc ⊗[R] Ge := LinearEquiv.ofBijective (Θ : B →ₐ[R] Gc ⊗[R] Ge).toLinearMap hΘ

  obtain ⟨w, hw⟩ := (TensorProduct.dualDistribEquiv R Gc Ge).surjective ((CartierDual.toDual R B θ) ∘ₗ eΘ.symm.toLinearMap)
  refine ⟨w, CartierDual.ext fun b => ?_⟩
  rw [Lam_apply qc πe Θ hΘΔ]
  have hw' : TensorProduct.dualDistrib R Gc Ge w = (CartierDual.toDual R B θ) ∘ₗ eΘ.symm.toLinearMap := by
    rw [← hw]; rfl
  rw [hw', LinearMap.comp_apply]
  have : eΘ.symm.toLinearMap (Θ b) = b := by
    have := eΘ.symm_apply_apply b
    exact this
  rw [this]
  rfl

end Ws50R3

theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : B →ₐc[ZMod p] Gc) (πe : B →ₐc[ZMod p] Ge) (Θ : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b))

    (N : ℕ) (hkill : PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) Ge (p ^ N) =
      (Algebra.ofId (ZMod p) Ge).comp (Bialgebra.counitAlgHom (ZMod p) Ge))
    (hGe : IsReduced Ge)
    (κ : Type) [CommRing κ] [Algebra (ZMod p) κ] [IsReduced κ]
    (χ : CartierDual (ZMod p) B →ₐ[ZMod p] κ)
    (g₁ g₂ : B →ₐc[ZMod p] B)
    (hg : (qc : B →ₐ[ZMod p] Gc).comp (g₁ : B →ₐ[ZMod p] B) = (qc : B →ₐ[ZMod p] Gc).comp (g₂ : B →ₐ[ZMod p] B)) :
    χ.comp (CartierDual.map g₁ : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) =
      χ.comp (CartierDual.map g₂ : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) := by
  classical

  have hgB : qc.comp g₁ = qc.comp g₂ := by
    apply DFunLike.ext
    intro b
    exact congrArg (fun (h : B →ₐ[ZMod p] Gc) => h b) hg

  have key : ∀ χ' χ'' : CartierDual (ZMod p) B →ₐ[ZMod p] κ,
      χ'.comp (CartierDual.mapAlgHom qc) = χ''.comp (CartierDual.mapAlgHom qc) → χ' = χ'' := by
    intro χ' χ'' hc

    have he : χ'.comp (CartierDual.mapAlgHom πe) = χ''.comp (CartierDual.mapAlgHom πe) := by
      refine AlgHom.ext fun ψ => ?_
      rw [CartierDual.algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp p Ge N hkill hGe κ
          (χ'.comp (CartierDual.mapAlgHom πe)) ψ,
        CartierDual.algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp p Ge N hkill hGe κ
          (χ''.comp (CartierDual.mapAlgHom πe)) ψ]

    have hΛ : χ'.comp (Ws50R3.Lam qc πe) = χ''.comp (Ws50R3.Lam qc πe) := by
      refine Algebra.TensorProduct.ext' fun φ ψ => ?_
      show χ' (Ws50R3.Lam qc πe (φ ⊗ₜ[ZMod p] ψ)) = χ'' (Ws50R3.Lam qc πe (φ ⊗ₜ[ZMod p] ψ))
      rw [Ws50R3.Lam_tmul, map_mul, map_mul]
      have h1 := congrArg (fun (h : CartierDual (ZMod p) Gc →ₐ[ZMod p] κ) => h φ) hc
      have h2 := congrArg (fun (h : CartierDual (ZMod p) Ge →ₐ[ZMod p] κ) => h ψ) he
      simp only [AlgHom.comp_apply] at h1 h2
      rw [h1, h2]
    refine AlgHom.ext fun θ => ?_
    obtain ⟨w, rfl⟩ := Ws50R3.Lam_surjective qc πe Θ hΘ hΘΔ θ
    exact congrArg (fun (h : _ →ₐ[ZMod p] κ) => h w) hΛ
  apply key
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
  have hm : ∀ g : B →ₐc[ZMod p] B, (CartierDual.map g : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B).comp
      (CartierDual.mapAlgHom qc) = ((CartierDual.map (qc.comp g)) : CartierDual (ZMod p) Gc →ₐ[ZMod p] CartierDual (ZMod p) B) := by
    intro g
    rw [CartierDual.map_comp]
    rfl
  rw [hm g₁, hm g₂, hgB]

end S_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
end P2MW
export P2MW.S_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp (solution)
