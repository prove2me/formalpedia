-- Prove2me | solution 1 for Deformation.DieudonneModule.bijective_prod_map_of_bijective_tensorProduct_comul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/54823214-be07-51b2-9592-66b6af1ac64f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul

open scoped TensorProduct
open MvPowerSeries

universe v

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [Bialgebra (ZMod p) B]
    (Gc Ge : Type v) [CommRing Gc] [Bialgebra (ZMod p) Gc] [CommRing Ge] [Bialgebra (ZMod p) Ge]
    (qc : B →ₐc[ZMod p] Gc) (πe : B →ₐc[ZMod p] Ge) (Θ : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hΘ : Function.Bijective Θ)
    (hΘapply : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b)) :
    Function.Bijective fun z : Deformation.DieudonneModule (ZMod p) p B =>
      (Deformation.DieudonneModule.map (ZMod p) p qc z, Deformation.DieudonneModule.map (ZMod p) p πe z) := by
  classical
  obtain ⟨i₁, i₂, q₁, q₂, -, -, hq₁, hq₂, e, he, -, -, -⟩ :=
    Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct p Gc Ge

  have key₁ : ∀ b, q₁ (Θ b) = qc b := by
    intro b
    have hφψ : (q₁ : Gc ⊗[ZMod p] Ge →ₐ[ZMod p] Gc).toLinearMap ∘ₗ
        (Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge)).toLinearMap =
        (qc : B →ₐ[ZMod p] Gc).toLinearMap ∘ₗ ((TensorProduct.rid (ZMod p) B).toLinearMap ∘ₗ
          LinearMap.lTensor B (Coalgebra.counit (R := ZMod p) (A := B))) := by
      refine TensorProduct.ext' fun x y => ?_
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
        LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_smul,
        BialgHom.coe_toAlgHom]
      rw [hq₁, CoalgHomClass.counit_comp_apply]
    have h := congrArg (fun f => f (Coalgebra.comul (R := ZMod p) b)) hφψ
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      BialgHom.coe_toAlgHom, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at h
    rw [hΘapply]
    exact h
  have key₂ : ∀ b, q₂ (Θ b) = πe b := by
    intro b
    have hφψ : (q₂ : Gc ⊗[ZMod p] Ge →ₐ[ZMod p] Ge).toLinearMap ∘ₗ
        (Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge)).toLinearMap =
        (πe : B →ₐ[ZMod p] Ge).toLinearMap ∘ₗ ((TensorProduct.lid (ZMod p) B).toLinearMap ∘ₗ
          LinearMap.rTensor B (Coalgebra.counit (R := ZMod p) (A := B))) := by
      refine TensorProduct.ext' fun x y => ?_
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, map_smul,
        BialgHom.coe_toAlgHom]
      rw [hq₂, CoalgHomClass.counit_comp_apply]
    have h := congrArg (fun f => f (Coalgebra.comul (R := ZMod p) b)) hφψ
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      BialgHom.coe_toAlgHom, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul] at h
    rw [hΘapply]
    exact h
  have hc₁ : q₁.comp Θ = qc := BialgHom.ext key₁
  have hc₂ : q₂.comp Θ = πe := BialgHom.ext key₂

  have hfun : (fun z : Deformation.DieudonneModule (ZMod p) p B =>
      (Deformation.DieudonneModule.map (ZMod p) p qc z, Deformation.DieudonneModule.map (ZMod p) p πe z)) =
      (fun w => e w) ∘ Deformation.DieudonneModule.map (ZMod p) p Θ := by
    funext z
    simp only [Function.comp_apply, he]
    rw [← hc₁, ← hc₂, Deformation.DieudonneModule.map_comp, Deformation.DieudonneModule.map_comp]

  set Θe : B ≃ₐc[ZMod p] Gc ⊗[ZMod p] Ge := BialgEquiv.ofBijective Θ hΘ with hΘe
  have hΘcoe : (Θe : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge) = Θ := by
    refine BialgHom.ext fun b => ?_
    rfl
  have hid : Θ.comp (Θe.symm : Gc ⊗[ZMod p] Ge →ₐc[ZMod p] B) = BialgHom.id (ZMod p) (Gc ⊗[ZMod p] Ge) := by
    refine BialgHom.ext fun x => ?_
    rw [BialgHom.coe_comp, Function.comp_apply]
    change Θe (Θe.symm x) = x
    exact Θe.apply_symm_apply x
  have hMΘ : Function.Bijective (Deformation.DieudonneModule.map (ZMod p) p Θ) := by
    refine ⟨Deformation.DieudonneModule.map_injective hΘ.1, fun w => ?_⟩
    refine ⟨Deformation.DieudonneModule.map (ZMod p) p (Θe.symm : Gc ⊗[ZMod p] Ge →ₐc[ZMod p] B) w, ?_⟩
    rw [← Deformation.DieudonneModule.map_comp, hid, Deformation.DieudonneModule.map_id]
  rw [hfun]
  exact e.bijective.comp hMΘ

end S_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul
end P2MW
export P2MW.S_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul (solution)
