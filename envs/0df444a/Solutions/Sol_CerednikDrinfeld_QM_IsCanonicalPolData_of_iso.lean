-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCanonicalPolData.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/81c04cb3-d7e0-5259-9654-ac42a011d529

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_of_iso
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace DII22

noncomputable def dualIso {X : Scheme.{0}} {M M' : X.Modules} (e : M ≅ M') :
    Scheme.Modules.dual M ≅ Scheme.Modules.dual M' :=
  ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm

noncomputable def mumfordBundleIso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {M M' : A.Modules} (e : M ≅ M') :
    mumfordBundle f L M ≅ mumfordBundle f L M' :=
  (Scheme.Modules.pullback (addMor f L)).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback (pullback.fst f f)).mapIso (dualIso e) ⊗ᵢ
      (Scheme.Modules.pullback (pullback.snd f f)).mapIso (dualIso e))

theorem locIsoOnBase_of_iso_left {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N N' P : X.Modules} (e : N ≅ N') (h : LocIsoOnBase g N' P) : LocIsoOnBase g N P := by
  intro s
  obtain ⟨U, hs, ⟨φ⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ φ⟩⟩

theorem locIsoOnBase_of_iso_right {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N P P' : X.Modules} (e : P ≅ P') (h : LocIsoOnBase g N P) : LocIsoOnBase g N P' := by
  intro s
  obtain ⟨U, hs, ⟨φ⟩⟩ := h s
  exact ⟨U, hs, ⟨φ ≪≫ (Scheme.Modules.pullback _).mapIso e⟩⟩

theorem locIsoOnBase_of_iso {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N N' : X.Modules} (e : N ≅ N') : LocIsoOnBase g N N' :=
  fun s => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

theorem isInvertible_of_iso {X : Scheme.{0}} {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M) (e : M ≅ M') :
    Scheme.Modules.IsInvertible M' := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := hM.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

end DII22

open DII22 in

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    {𝓛 𝓛' : A.Modules} (e : 𝓛 ≅ 𝓛')
    (h : CerednikDrinfeld.QM.IsCanonicalPolData f L act act_over star 𝓛) :
    CerednikDrinfeld.QM.IsCanonicalPolData f L act act_over star 𝓛' := by
  obtain ⟨hinv, hsym, hK2, ⟨S', iS', aS', hff, hsqrt⟩, hpos, hros⟩ := h
  refine ⟨isInvertible_of_iso hinv e, ?_, ?_, ⟨S', iS', aS', hff, ?_⟩, ?_, ?_⟩
  ·
    exact locIsoOnBase_of_iso_right f e
      (locIsoOnBase_of_iso_left f ((Scheme.Modules.pullback (negMor f L)).mapIso e.symm) hsym)
  ·
    intro R _ t x
    rw [← hK2 R t x]
    constructor
    · exact fun hx => locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso (mumfordBundleIso f L e)) hx
    · exact fun hx => locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso (mumfordBundleIso f L e.symm)) hx
  ·
    intro L' hL'
    obtain ⟨𝓛₀, h₀, hK₀, hsq⟩ := hsqrt L' hL'
    exact ⟨𝓛₀, h₀, hK₀, locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback _).mapIso e.symm) hsq⟩
  ·
    intro k _ _ sk
    rw [← AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase f (locIsoOnBase_of_iso f e) k sk]
    exact hpos k sk
  ·
    intro b
    exact locIsoOnBase_of_iso_right _ ((Scheme.Modules.pullback _).mapIso (mumfordBundleIso f L e))
      (locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback _).mapIso (mumfordBundleIso f L e.symm)) (hros b))

end S_CerednikDrinfeld_QM_IsCanonicalPolData_of_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_of_iso (solution)
