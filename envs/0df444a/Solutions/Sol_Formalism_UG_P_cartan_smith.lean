-- Prove2me | solution 1 for Formalism.UG.P.cartan_smith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:11.421071+00:00
-- url     : https://prove2.me/submissions/383ee542-4df3-4926-a927-d6266af16001

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_mulVec_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (G : Matrix n n R) (hG : G.det ≠ 0) :
    ∃ P C : Matrix n n R, IsUnit P.det ∧ IsUnit C.det ∧ ∃ a : n → R, (∀ i, a i ≠ 0) ∧
      G = P * Matrix.diagonal a * C := by
  have inj := cartan_mulVec_injective G hG
  let N := LinearMap.range (Matrix.mulVecLin G)
  let e0 : (n → R) ≃ₗ[R] N := LinearEquiv.ofInjective _ inj
  have hrank : Module.finrank R N = Module.finrank R (n → R) := e0.finrank_eq.symm
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun R n) hrank
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    apply ab'.ne_zero i
    apply Subtype.coe_injective
    simp [hab i, hi]
  let e : (n → R) ≃ₗ[R] (n → R) :=
    e0.trans (ab'.repr.trans (Finsupp.linearEquivFunOnFinite R R n))
  let P := (Pi.basisFun R n).toMatrix b'
  let C := LinearMap.toMatrix' (e : (n → R) →ₗ[R] (n → R))
  let C' := LinearMap.toMatrix' (e.symm : (n → R) →ₗ[R] (n → R))
  have hCC : C * C' = 1 := by
    simp only [C, C', ← LinearMap.toMatrix'_comp]
    have : (e : (n → R) →ₗ[R] (n → R)) ∘ₗ (e.symm : (n → R) →ₗ[R] (n → R)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hP : IsUnit P.det := by
    have := (Pi.basisFun R n).invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨P, C, hP, Matrix.isUnit_det_of_right_inverse hCC, a, ha, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hC : C *ᵥ x = e x := LinearMap.toMatrix'_mulVec _ x
  rw [hC]
  have hx : G *ᵥ x = ((e0 x : N) : n → R) := by
    show G *ᵥ x = ((LinearEquiv.ofInjective _ inj x : N) : n → R)
    rw [LinearEquiv.ofInjective_apply]; rfl
  rw [hx]
  conv_lhs => rw [← ab'.sum_repr (e0 x)]
  funext k
  simp only [Submodule.coe_sum, Submodule.coe_smul, hab, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [P, e, Module.Basis.toMatrix_apply, Finsupp.linearEquivFunOnFinite_apply]
  ring
end Formalism.UG.P
