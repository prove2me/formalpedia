-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/123747b2-b0b5-5c7f-8b0f-d09c251867d6

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld

namespace Ws23TangentLieQuot

open CerednikDrinfeld CerednikDrinfeld.FormalODModule CerednikDrinfeld.GradedCartierModuleData MvFormalGroup MvFormalGroup.CartierModule

variable (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
  (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))

noncomputable def tangentₛₗ :
    MvFormalGroup.CartierModule p X.F →ₛₗ[(WittVector.constantCoeff : WittVector p B →+* B)] (Fin 2 → B) where
  toFun := tangent
  map_add' := map_add tangent
  map_smul' w f := by rw [tangent_smul_witt, WittVector.constantCoeff_apply]

@[scoped simp] theorem tangentₛₗ_apply (f : MvFormalGroup.CartierModule p X.F) : tangentₛₗ p X f = tangent f := rfl

theorem vRange_le_ker :
    (X.toGradedCartierModuleData j hc).vRange ≤ LinearMap.ker (tangentₛₗ p X) := by
  rintro f ⟨g, rfl⟩
  change tangent (verschiebungInt g) = 0
  rw [verschiebungInt_apply_eq_verschiebung]
  exact ((tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq p X.F).2 _).2 ⟨g, rfl⟩

noncomputable def lambdaₛₗ :
    (X.toGradedCartierModuleData j hc).LieQuot →ₛₗ[(WittVector.constantCoeff : WittVector p B →+* B)] (Fin 2 → B) :=
  (X.toGradedCartierModuleData j hc).vRange.liftQ (tangentₛₗ p X) (vRange_le_ker p j X hc)

theorem lambdaₛₗ_mkQ (m : MvFormalGroup.CartierModule p X.F) :
    lambdaₛₗ p j X hc ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = tangent m := rfl

theorem lambdaₛₗ_injective : Function.Injective (lambdaₛₗ p j X hc) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [LinearMap.mem_ker, lambdaₛₗ_mkQ] at hq
  obtain ⟨g, hg⟩ := ((tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq p X.F).2 m).1 hq
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨g, ?_⟩
  show verschiebungInt g = m
  rw [verschiebungInt_apply_eq_verschiebung, hg]

theorem lambdaₛₗ_surjective : Function.Surjective (lambdaₛₗ p j X hc) := by
  intro v
  obtain ⟨m, hm⟩ := (tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq p X.F).1 v
  exact ⟨(X.toGradedCartierModuleData j hc).vRange.mkQ m, by rw [lambdaₛₗ_mkQ, hm]⟩

end Ws23TangentLieQuot
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent.Ws23TangentLieQuot"

open Ws23TangentLieQuot in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) :
    ∃ Λ : (X.toGradedCartierModuleData j hc).LieQuot ≃+ (Fin 2 → B),
      (∀ m : MvFormalGroup.CartierModule p X.F,
          Λ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = MvFormalGroup.CartierModule.tangent m) ∧
      (∀ (w : WittVector p B) (q : (X.toGradedCartierModuleData j hc).LieQuot),
          Λ (w • q) = w.coeff 0 • Λ q) := by
  refine ⟨AddEquiv.ofBijective (lambdaₛₗ p j X hc).toAddMonoidHom
      ⟨lambdaₛₗ_injective p j X hc, lambdaₛₗ_surjective p j X hc⟩, fun m => rfl, fun w q => ?_⟩
  show lambdaₛₗ p j X hc (w • q) = w.coeff 0 • lambdaₛₗ p j X hc q
  rw [LinearMap.map_smulₛₗ, WittVector.constantCoeff_apply]

end S_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent (solution)
