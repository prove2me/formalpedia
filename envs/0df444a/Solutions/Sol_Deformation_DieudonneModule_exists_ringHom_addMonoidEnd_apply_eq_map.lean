-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_ringHom_addMonoidEnd_apply_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/45cbbabb-348b-5d2d-abb2-3c868c2a2f5f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_ringHom_addMonoidEnd_apply_eq_map

set_option autoImplicit false
open scoped TensorProduct

theorem solution
    (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime]
    {A : Type} [CommRing A] [Bialgebra R A]
    {κ : Type} [CommRing κ] (θ : κ → (A →ₐc[R] A))
    (hone : θ 1 = BialgHom.id R A)
    (hmul : ∀ a b : κ, θ (a * b) = (θ a).comp (θ b))
    (hadd : ∀ a b : κ, (θ (a + b) : A →ₐ[R] A).toLinearMap =
      LinearMap.mul' R A ∘ₗ TensorProduct.map (θ a : A →ₐ[R] A).toLinearMap (θ b : A →ₐ[R] A).toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := A)) :
    ∃ Θ : κ →+* AddMonoid.End (Deformation.DieudonneModule R p A),
      ∀ (a : κ) (x : Deformation.DieudonneModule R p A),
        Θ a x = Deformation.DieudonneModule.map R p (θ a) x := by

  have hadd' : ∀ (a b : κ) (x : Deformation.DieudonneModule R p A),
      Deformation.DieudonneModule.map R p (θ (a + b)) x =
        Deformation.DieudonneModule.map R p (θ a) x + Deformation.DieudonneModule.map R p (θ b) x :=
    fun a b x =>
      Deformation.DieudonneModule.map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul R p
        (θ a) (θ b) (θ (a + b)) (hadd a b) x
  have hzero : ∀ x : Deformation.DieudonneModule R p A, Deformation.DieudonneModule.map R p (θ 0) x = 0 := by
    intro x
    have h := hadd' 0 0 x
    rw [add_zero] at h

    have : Deformation.DieudonneModule.map R p (θ 0) x + Deformation.DieudonneModule.map R p (θ 0) x =
        Deformation.DieudonneModule.map R p (θ 0) x + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  refine ⟨{ toFun := fun a => Deformation.DieudonneModule.map R p (θ a)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a x => rfl⟩
  · apply AddMonoidHom.ext; intro x
    show Deformation.DieudonneModule.map R p (θ 1) x = x
    rw [hone]; exact Deformation.DieudonneModule.map_id x
  · intro a b; apply AddMonoidHom.ext; intro x
    show Deformation.DieudonneModule.map R p (θ (a * b)) x =
      Deformation.DieudonneModule.map R p (θ a) (Deformation.DieudonneModule.map R p (θ b) x)
    rw [hmul]; exact Deformation.DieudonneModule.map_comp (θ b) (θ a) x
  · apply AddMonoidHom.ext; intro x
    exact hzero x
  · intro a b; apply AddMonoidHom.ext; intro x
    exact hadd' a b x

end S_Deformation_DieudonneModule_exists_ringHom_addMonoidEnd_apply_eq_map
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_ringHom_addMonoidEnd_apply_eq_map (solution)
