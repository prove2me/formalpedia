-- Prove2me | solution 1 for BialgHom.exists_coe_eq_of_forall_withConv_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3c98348c-e5c9-576c-8704-fd1e44891cf5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_BialgHom_exists_coe_eq_of_forall_withConv_comp

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {H : Type u} [CommRing H] [Bialgebra R H] {H' : Type u} [CommRing H'] [Bialgebra R H']
    (φ : H →ₐ[R] H')
    (hsep : ∀ x : H' ⊗[R] H', (∀ θ : H' ⊗[R] H' →ₐ[R] K, θ x = 0) → x = 0)
    (hone : (1 : WithConv (H' →ₐ[R] K)).ofConv.comp φ = (1 : WithConv (H →ₐ[R] K)).ofConv)
    (hmul : ∀ χ χ' : WithConv (H' →ₐ[R] K),
      (χ * χ').ofConv.comp φ = (WithConv.toConv (χ.ofConv.comp φ) * WithConv.toConv (χ'.ofConv.comp φ)).ofConv) :
    ∃ ψ : H →ₐc[R] H', (ψ : H →ₐ[R] H') = φ := by

  have hcounit : (Bialgebra.counitAlgHom R H').comp φ = Bialgebra.counitAlgHom R H := by
    ext h
    apply hinj
    have := congr($hone h)
    simpa [AlgHom.convOne_def] using this

  have hcomul : (Algebra.TensorProduct.map φ φ).comp (Bialgebra.comulAlgHom R H) = (Bialgebra.comulAlgHom R H').comp φ := by
    ext h
    rw [← sub_eq_zero]
    apply hsep
    intro θ
    set χ : H' →ₐ[R] K := θ.comp Algebra.TensorProduct.includeLeft with hχ
    set χ' : H' →ₐ[R] K := θ.comp Algebra.TensorProduct.includeRight with hχ'
    have hθ : θ = Algebra.TensorProduct.lift χ χ' (fun _ _ => Commute.all _ _) := by
      ext a <;> simp [hχ, hχ']
    rw [hθ, map_sub, sub_eq_zero]
    have h1 := congr($(hmul (.toConv χ) (.toConv χ')) h)
    simp only [AlgHom.convMul_def, WithConv.ofConv_toConv, AlgHom.comp_apply] at h1

    have e1 : ∀ (f g : H →ₐ[R] K) (z : H ⊗[R] H),
        Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z =
          (Algebra.TensorProduct.lmul' R (S := K)) (Algebra.TensorProduct.map f g z) := by
      intro f g z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      | add a b ha hb => simp [map_add, ha, hb]
    have e2 : ∀ (f g : H' →ₐ[R] K) (z : H' ⊗[R] H'),
        Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z =
          (Algebra.TensorProduct.lmul' R (S := K)) (Algebra.TensorProduct.map f g z) := by
      intro f g z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      | add a b ha hb => simp [map_add, ha, hb]
    have e3 : ∀ z : H ⊗[R] H, Algebra.TensorProduct.lift χ χ' (fun _ _ => Commute.all _ _) (Algebra.TensorProduct.map φ φ z) =
        Algebra.TensorProduct.lift (χ.comp φ) (χ'.comp φ) (fun _ _ => Commute.all _ _) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.lift_tmul]
      | add a b ha hb => simp [map_add, ha, hb]
    simp only [AlgHom.comp_apply]
    rw [e3, e1, e2]
    exact h1.symm
  exact ⟨BialgHom.ofAlgHom φ hcounit hcomul, rfl⟩

end S_BialgHom_exists_coe_eq_of_forall_withConv_comp
end P2MW
export P2MW.S_BialgHom_exists_coe_eq_of_forall_withConv_comp (solution)
