-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0ffa568a-4374-581f-8fbc-e5e6ccda00d6

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_iso_of_polarisedAbelianScheme_iso

import Theorems.Thm_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_refl_symm_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_isPullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_IsPullback_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback__5e6a0e
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

namespace PQH_E

noncomputable def specHom {A B : CommRingCat.{0}} (g : Spec A ⟶ Spec B) : (B : Type) →+* (A : Type) :=
  (Spec.preimage g).hom

theorem specMap_specHom {A B : CommRingCat.{0}} (g : Spec A ⟶ Spec B) :
    Spec.map (CommRingCat.ofHom (specHom g)) = g := by
  rw [specHom, CommRingCat.ofHom_hom, Spec.map_preimage]

end PQH_E

open PQH_E in
theorem PQH.exists_ringHom_isPullback_qmStructure_iso_of_specMap_comp_pt_factors_satisfying
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ) {m : ℕ}
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM}
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli 2 36 m Q M πM pt)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')
    (U : M.affineOpens) (XU : PolarisedAbelianScheme 2 36 m Γ(M, U)) (hQU : Q Γ(M, U) XU)
    (hXU : (pt Γ(M, U) (U.2.fromSpec ≫ πM) ⟨XU, hQU⟩).1 = U.2.fromSpec)
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X)
    (S' : Type) [CommRing S'] (ψ : S →+* S')
    (hψ : Set.range (Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1).base ⊆ (U : Set M)) :
    ∃ (φ : Γ(M, U) →+* S')
      (_ : Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1)
      (X' : PolarisedAbelianScheme 2 36 m S') (t' : QMStructure Λ star β X')
      (_ : PolarisedAbelianScheme.IsPullback ψ X X') (_ : QMStructure.IsPullback ψ t t')
      (X'' : PolarisedAbelianScheme 2 36 m S') (_ : PolarisedAbelianScheme.IsPullback φ XU X'')
      (t'' : QMStructure Λ star β X''), QMStructure.Iso t' t'' := by

  let l : Spec (CommRingCat.of S') ⟶ Spec Γ(M, U) :=
    IsOpenImmersion.lift U.2.fromSpec (Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1)
      (by rw [IsAffineOpen.range_fromSpec]; exact hψ)
  have hl : l ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1 := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(M, U) →+* S' := specHom l
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1 := by
    rw [specMap_specHom]; exact hl

  obtain ⟨X', hX'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback ψ X
  obtain ⟨t', ht'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback ψ hX' t
  obtain ⟨X'', hX''⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φ XU

  have hs : Spec.map (CommRingCat.ofHom φ) ≫ (U.2.fromSpec ≫ πM) = Spec.map (CommRingCat.ofHom ψ) ≫ s := by
    rw [← Category.assoc, hφ, Category.assoc, (pt S s ⟨X, hQ S s X t⟩).2]
  have h1 := hM.pt_pullback S S' ψ s (Spec.map (CommRingCat.ofHom ψ) ≫ s) rfl ⟨X, hQ S s X t⟩ ⟨X', hQ S' (Spec.map (CommRingCat.ofHom ψ) ≫ s) X' t'⟩ hX'
  have h2 := hM.pt_pullback Γ(M, U) S' φ (U.2.fromSpec ≫ πM) (Spec.map (CommRingCat.ofHom ψ) ≫ s) hs ⟨XU, hQU⟩ ⟨X'', hQbc _ _ φ XU X'' hX'' hQU⟩ hX''
  rw [hXU, hφ] at h2
  have hiso : PolarisedAbelianScheme.Iso X' X'' :=
    hM.pt_injective S' (Spec.map (CommRingCat.ofHom ψ) ≫ s) ⟨X', hQ S' (Spec.map (CommRingCat.ofHom ψ) ≫ s) X' t'⟩
      ⟨X'', hQbc _ _ φ XU X'' hX'' hQU⟩ (Subtype.ext (h1.trans h2.symm))

  obtain ⟨t'', htt⟩ :=
    AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso hiso t'
  exact ⟨φ, hφ, X', t', hX', ht', X'', hX'', t'', htt⟩

theorem PQH9.ptZ_comp_openImmersion_eq_of_iso_of_iso_satisfying
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ) {m : ℕ}
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM}
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli 2 36 m Q M πM pt)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')
    (hsep : ∀ U V : M.affineOpens, IsAffineOpen ((U : M.Opens) ⊓ (V : M.Opens)))
    {M₁ : Scheme.{0}} (f : M₁ ⟶ M)
    (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U))
    (hQU : ∀ U : M.affineOpens, Q Γ(M, U) (XU U))
    (hXU : ∀ U : M.affineOpens, (pt Γ(M, U) (U.2.fromSpec ≫ πM) ⟨XU U, hQU U⟩).1 = U.2.fromSpec)
    (Z : M.affineOpens → Scheme.{0}) (ζ : ∀ U : M.affineOpens, Z U ⟶ Spec Γ(M, U))
    (ι : ∀ U : M.affineOpens, Z U ⟶ M₁) [∀ U : M.affineOpens, IsOpenImmersion (ι U)]
    (hsq : ∀ U : M.affineOpens, IsPullback (ι U) (ζ U) f U.2.fromSpec)
    (ptZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
      PolarisedAbelianScheme.IsPullback φ (XU U) X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U))
    (hiso : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.Iso s' s'' → (ptZ U T φ X' hX' s').1 = (ptZ U T φ X'' hX'' s'').1)
    (hcompat : ∀ (U V : M.affineOpens) (hVU : (V : M.Opens) ≤ (U : M.Opens)) (T : Type) [CommRing T]
      (φ : Γ(M, V) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU V) X')
      (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE hVU).op).hom) (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.Iso s' s'' →
      (ptZ V T φ X' hX' s').1 ≫ ι V = (ptZ U T (φ.comp (M.presheaf.map (homOfLE hVU).op).hom) X'' hX'' s'').1 ≫ ι U)

    (S' : Type) [CommRing S'] (p : Spec (CommRingCat.of S') ⟶ M)
    (U₁ U₂ : M.affineOpens) (φ₁ : Γ(M, U₁) →+* S') (φ₂ : Γ(M, U₂) →+* S')
    (hφ₁ : Spec.map (CommRingCat.ofHom φ₁) ≫ U₁.2.fromSpec = p)
    (hφ₂ : Spec.map (CommRingCat.ofHom φ₂) ≫ U₂.2.fromSpec = p)
    (X₁ X₂ : PolarisedAbelianScheme 2 36 m S')
    (hX₁ : PolarisedAbelianScheme.IsPullback φ₁ (XU U₁) X₁) (hX₂ : PolarisedAbelianScheme.IsPullback φ₂ (XU U₂) X₂)
    (t₁ : QMStructure Λ star β X₁) (t₂ : QMStructure Λ star β X₂) (h₁₂ : QMStructure.Iso t₁ t₂) :
    (ptZ U₁ S' φ₁ X₁ hX₁ t₁).1 ≫ ι U₁ = (ptZ U₂ S' φ₂ X₂ hX₂ t₂).1 ≫ ι U₂ := by
  classical

  let W : M.affineOpens := ⟨(U₁ : M.Opens) ⊓ (U₂ : M.Opens), hsep U₁ U₂⟩
  have hW₁ : (W : M.Opens) ≤ (U₁ : M.Opens) := inf_le_left
  have hW₂ : (W : M.Opens) ≤ (U₂ : M.Opens) := inf_le_right

  have hr₁ : Set.range p.base ⊆ (U₁ : Set M) := by
    rw [← hφ₁]; rintro _ ⟨y, rfl⟩; exact U₁.2.range_fromSpec.subset ⟨_, rfl⟩
  have hr₂ : Set.range p.base ⊆ (U₂ : Set M) := by
    rw [← hφ₂]; rintro _ ⟨y, rfl⟩; exact U₂.2.range_fromSpec.subset ⟨_, rfl⟩
  have hrW : Set.range p.base ⊆ Set.range W.2.fromSpec.base := by
    rw [W.2.range_fromSpec]
    exact fun x hx => ⟨hr₁ hx, hr₂ hx⟩

  obtain ⟨φW, hφW⟩ : ∃ φW : Γ(M, W) →+* S', Spec.map (CommRingCat.ofHom φW) ≫ W.2.fromSpec = p := by
    refine ⟨(Spec.preimage (IsOpenImmersion.lift W.2.fromSpec p hrW)).hom, ?_⟩
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

  have key : ∀ (U : M.affineOpens) (hWU : (W : M.Opens) ≤ (U : M.Opens)) (φ : Γ(M, U) →+* S'),
      Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = p →
      φ = φW.comp (M.presheaf.map (homOfLE hWU).op).hom := by
    intro U hWU φ hφ
    have h1 : Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec =
        Spec.map (CommRingCat.ofHom (φW.comp (M.presheaf.map (homOfLE hWU).op).hom)) ≫ U.2.fromSpec := by
      rw [hφ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        U.2.map_fromSpec W.2 (homOfLE hWU).op, hφW]
    have h2 := Spec.map_injective ((cancel_mono U.2.fromSpec).mp h1)
    exact congrArg CommRingCat.Hom.hom h2
  obtain rfl := key U₁ hW₁ φ₁ hφ₁
  obtain rfl := key U₂ hW₂ φ₂ hφ₂

  obtain ⟨XW, hXW⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback φW (XU W)
  have hs₁ : Spec.map (CommRingCat.ofHom (φW.comp (M.presheaf.map (homOfLE hW₁).op).hom)) ≫ (U₁.2.fromSpec ≫ πM) =
      p ≫ πM := by rw [← Category.assoc, hφ₁]
  have hsW : Spec.map (CommRingCat.ofHom φW) ≫ (W.2.fromSpec ≫ πM) = p ≫ πM := by rw [← Category.assoc, hφW]
  have hpt₁ := hM.pt_pullback _ S' _ (U₁.2.fromSpec ≫ πM) (p ≫ πM) hs₁ ⟨XU U₁, hQU U₁⟩ ⟨X₁, hQbc _ _ _ (XU U₁) X₁ hX₁ (hQU U₁)⟩ hX₁
  have hptW := hM.pt_pullback _ S' _ (W.2.fromSpec ≫ πM) (p ≫ πM) hsW ⟨XU W, hQU W⟩ ⟨XW, hQbc _ _ _ (XU W) XW hXW (hQU W)⟩ hXW
  rw [hXU U₁, hφ₁] at hpt₁
  rw [hXU W, hφW] at hptW
  have hisoX : PolarisedAbelianScheme.Iso X₁ XW :=
    hM.pt_injective S' (p ≫ πM) ⟨X₁, hQbc _ _ _ (XU U₁) X₁ hX₁ (hQU U₁)⟩ ⟨XW, hQbc _ _ _ (XU W) XW hXW (hQU W)⟩
      (Subtype.ext (hpt₁.trans hptW.symm))
  obtain ⟨tW, htW⟩ :=
    AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso hisoX t₁
  have Q := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans
    (Λ := Λ) (star := star) (β := β) (d := 36) (m := m) (S := S')
  have hW1 : QMStructure.Iso tW t₁ := Q.2.1 _ _ _ _ htW
  have hW2 : QMStructure.Iso tW t₂ := Q.2.2 _ _ _ _ _ _ hW1 h₁₂
  have e₁ := hcompat U₁ W hW₁ S' φW XW X₁ hXW hX₁ tW t₁ hW1
  have e₂ := hcompat U₂ W hW₂ S' φW XW X₂ hXW hX₂ tW t₂ hW2
  exact e₁.symm.trans e₂

namespace C7R4

def IsChartAnswer
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ) {m : ℕ}
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop}
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    {M₁ : Scheme.{0}} (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U))
    (Z : M.affineOpens → Scheme.{0}) (ζ : ∀ U : M.affineOpens, Z U ⟶ Spec Γ(M, U))
    (ι : ∀ U : M.affineOpens, Z U ⟶ M₁)
    (ptZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
      PolarisedAbelianScheme.IsPullback φ (XU U) X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U))
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X)
    (S' : Type) [CommRing S'] (ψ : S →+* S') (v : Spec (CommRingCat.of S') ⟶ M₁) : Prop :=
  ∃ (U : M.affineOpens) (φ : Γ(M, U) →+* S')
    (_ : Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1)
    (X' : PolarisedAbelianScheme 2 36 m S') (t' : QMStructure Λ star β X')
    (_ : PolarisedAbelianScheme.IsPullback ψ X X') (_ : QMStructure.IsPullback ψ t t')
    (X'' : PolarisedAbelianScheme 2 36 m S') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
    (t'' : QMStructure Λ star β X'') (_ : QMStructure.Iso t' t''),
    v = (ptZ U S' φ X'' hX'' t'').1 ≫ ι U

end C7R4

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ) {m : ℕ}
    {𝒪 : Type} [CommRing 𝒪] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme 2 36 m S → Prop}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying 2 36 m Q S → SchemeHomOver s πM}
    (hM : PolarisedAbelianScheme.Satisfying.IsFineModuli 2 36 m Q M πM pt)
    (hQ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : PolarisedAbelianScheme 2 36 m S), QMStructure Λ star β X → Q S X)
    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S'),
      PolarisedAbelianScheme.IsPullback φ X X' → Q S X → Q S' X')
    (hsep : ∀ U V : M.affineOpens, IsAffineOpen ((U : M.Opens) ⊓ (V : M.Opens)))
    {M₁ : Scheme.{0}} (f : M₁ ⟶ M)

    (XU : ∀ U : M.affineOpens, PolarisedAbelianScheme 2 36 m Γ(M, U))
    (hQU : ∀ U : M.affineOpens, Q Γ(M, U) (XU U))
    (hXU : ∀ U : M.affineOpens, (pt Γ(M, U) (U.2.fromSpec ≫ πM) ⟨XU U, hQU U⟩).1 = U.2.fromSpec)
    (Z : M.affineOpens → Scheme.{0}) (ζ : ∀ U : M.affineOpens, Z U ⟶ Spec Γ(M, U))
    (ι : ∀ U : M.affineOpens, Z U ⟶ M₁) [∀ U : M.affineOpens, IsOpenImmersion (ι U)]
    (hsq : ∀ U : M.affineOpens, IsPullback (ι U) (ζ U) f U.2.fromSpec)
    (ptZ : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' : PolarisedAbelianScheme 2 36 m T),
      PolarisedAbelianScheme.IsPullback φ (XU U) X' → QMStructure Λ star β X' →
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ζ U))

    (hnat : ∀ (U : M.affineOpens) (T T' : Type) [CommRing T] [CommRing T'] (φ : Γ(M, U) →+* T)
      (φ' : Γ(M, U) →+* T') (ψ : T →+* T') (hψ : ψ.comp φ = φ')
      (X' : PolarisedAbelianScheme 2 36 m T) (X'' : PolarisedAbelianScheme 2 36 m T')
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ' (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.IsPullback ψ s' s'' →
      (ptZ U T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ U T φ X' hX' s').1)

    (hiso : ∀ (U : M.affineOpens) (T : Type) [CommRing T] (φ : Γ(M, U) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU U) X') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.Iso s' s'' → (ptZ U T φ X' hX' s').1 = (ptZ U T φ X'' hX'' s'').1)

    (hcompat : ∀ (U V : M.affineOpens) (hVU : (V : M.Opens) ≤ (U : M.Opens)) (T : Type) [CommRing T]
      (φ : Γ(M, V) →+* T) (X' X'' : PolarisedAbelianScheme 2 36 m T)
      (hX' : PolarisedAbelianScheme.IsPullback φ (XU V) X')
      (hX'' : PolarisedAbelianScheme.IsPullback (φ.comp (M.presheaf.map (homOfLE hVU).op).hom) (XU U) X'')
      (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
      QMStructure.Iso s' s'' →
      (ptZ V T φ X' hX' s').1 ≫ ι V = (ptZ U T (φ.comp (M.presheaf.map (homOfLE hVU).op).hom) X'' hX'' s'').1 ≫ ι U)
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (X : PolarisedAbelianScheme 2 36 m S) (t : QMStructure Λ star β X) :
    ∃ q : SchemeHomOver s (f ≫ πM),
      q.1 ≫ f = (pt S s ⟨X, hQ S s X t⟩).1 ∧
      ∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (U : M.affineOpens) (φ : Γ(M, U) →+* S'),
        Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S s ⟨X, hQ S s X t⟩).1 →
        ∀ (X' : PolarisedAbelianScheme 2 36 m S') (t' : QMStructure Λ star β X'),
        PolarisedAbelianScheme.IsPullback ψ X X' → QMStructure.IsPullback ψ t t' →
        ∀ (X'' : PolarisedAbelianScheme 2 36 m S') (hX'' : PolarisedAbelianScheme.IsPullback φ (XU U) X'')
          (t'' : QMStructure Λ star β X''), QMStructure.Iso t' t'' →
        Spec.map (CommRingCat.ofHom ψ) ≫ q.1 = (ptZ U S' φ X'' hX'' t'').1 ≫ ι U := by
  classical
  set p := (pt S s ⟨X, hQ S s X t⟩).1 with hp

  have isymm : ∀ (S' : Type) [CommRing S'] {X₁ X₂ : PolarisedAbelianScheme 2 36 m S'} (t₁ : QMStructure Λ star β X₁)
      (t₂ : QMStructure Λ star β X₂), QMStructure.Iso t₁ t₂ → QMStructure.Iso t₂ t₁ :=
    fun S' _ _ _ t₁ t₂ h => (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans (S := S')).2.1 _ _ t₁ t₂ h
  have itrans : ∀ (S' : Type) [CommRing S'] {X₁ X₂ X₃ : PolarisedAbelianScheme 2 36 m S'} (t₁ : QMStructure Λ star β X₁)
      (t₂ : QMStructure Λ star β X₂) (t₃ : QMStructure Λ star β X₃),
      QMStructure.Iso t₁ t₂ → QMStructure.Iso t₂ t₃ → QMStructure.Iso t₁ t₃ :=
    fun S' _ _ _ _ t₁ t₂ t₃ h h' =>
      (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.refl_symm_trans (S := S')).2.2 _ _ _ t₁ t₂ t₃ h h'

  have F2 : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (v₁ v₂ : Spec (CommRingCat.of S') ⟶ M₁),
      C7R4.IsChartAnswer Λ star β pt hQ XU Z ζ ι ptZ S s X t S' ψ v₁ →
      C7R4.IsChartAnswer Λ star β pt hQ XU Z ζ ι ptZ S s X t S' ψ v₂ → v₁ = v₂ := by
    intro S' _ ψ v₁ v₂ h₁ h₂
    obtain ⟨U₁, φ₁, hφ₁, X'₁, t'₁, hX'₁, ht'₁, X''₁, hX''₁, t''₁, hi₁, rfl⟩ := h₁
    obtain ⟨U₂, φ₂, hφ₂, X'₂, t'₂, hX'₂, ht'₂, X''₂, hX''₂, t''₂, hi₂, rfl⟩ := h₂
    have h12 : QMStructure.Iso t''₁ t''₂ :=
      itrans S' _ _ _ (isymm S' _ _ hi₁)
        (itrans S' _ _ _ (AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_isPullback_of_isPullback ψ ht'₁ ht'₂) hi₂)
    exact PQH9.ptZ_comp_openImmersion_eq_of_iso_of_iso_satisfying Λ star β hM hQ hQbc hsep f XU hQU hXU Z ζ ι hsq ptZ hiso hcompat
      S' (Spec.map (CommRingCat.ofHom ψ) ≫ p) U₁ U₂ φ₁ φ₂ hφ₁ hφ₂ X''₁ X''₂ hX''₁ hX''₂ t''₁ t''₂ h12

  let adm : ∀ (S' : Type) [CommRing S'], (S →+* S') → Prop :=
    fun S' _ ψ => ∃ U : M.affineOpens, Set.range (Spec.map (CommRingCat.ofHom ψ) ≫ p).base ⊆ (U : Set M)
  have hadm : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (χ : S' →+* S''),
      adm S' ψ → adm S'' (χ.comp ψ) := by
    intro S' S'' _ _ ψ χ ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro _ ⟨y, rfl⟩
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    exact hU ⟨(Spec.map (CommRingCat.ofHom χ)).base y, rfl⟩

  have F1 : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S'), adm S' ψ →
      ∃ v, C7R4.IsChartAnswer Λ star β pt hQ XU Z ζ ι ptZ S s X t S' ψ v := by
    intro S' _ ψ ⟨U, hU⟩
    obtain ⟨φ, hφ, X', t', hX', ht', X'', hX'', t'', hi⟩ :=
      PQH.exists_ringHom_isPullback_qmStructure_iso_of_specMap_comp_pt_factors_satisfying
        Λ star β hM hQ hQbc U (XU U) (hQU U) (hXU U) S s X t S' ψ hU
    exact ⟨_, U, φ, hφ, X', t', hX', ht', X'', hX'', t'', hi, rfl⟩

  have F3 : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (χ : S' →+* S'')
      (v : Spec (CommRingCat.of S') ⟶ M₁),
      C7R4.IsChartAnswer Λ star β pt hQ XU Z ζ ι ptZ S s X t S' ψ v →
      C7R4.IsChartAnswer Λ star β pt hQ XU Z ζ ι ptZ S s X t S'' (χ.comp ψ) (Spec.map (CommRingCat.ofHom χ) ≫ v) := by
    intro S' S'' _ _ ψ χ v h
    obtain ⟨U, φ, hφ, X', t', hX', ht', X'', hX'', t'', hi, rfl⟩ := h

    obtain ⟨X'c, hX'c⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback χ X'
    obtain ⟨t'c, ht'c⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback χ hX'c t'
    obtain ⟨X''c, hX''c⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback χ X''
    obtain ⟨t''c, ht''c⟩ := AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback χ hX''c t''
    have hX''cc : PolarisedAbelianScheme.IsPullback (χ.comp φ) (XU U) X''c :=
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans φ χ (XU U) X'' X''c hX'' hX''c
    refine ⟨U, χ.comp φ, ?_, X'c, t'c,
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans ψ χ X X' X'c hX' hX'c,
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.IsPullback.trans ψ χ ht' ht'c,
      X''c, hX''cc, t''c,
      AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.of_isPullback_of_isPullback χ hi ht'c ht''c, ?_⟩
    · rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ, CommRingCat.ofHom_comp, Spec.map_comp,
        Category.assoc]
    · have hn := hnat U S' S'' φ (χ.comp φ) χ rfl X'' X''c hX'' hX''cc t'' t''c ht''c
      rw [← Category.assoc, ← hn]

  let z : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S'), adm S' ψ → (Spec (CommRingCat.of S') ⟶ M₁) :=
    fun S' _ ψ h => (F1 S' ψ h).choose
  have hzspec : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (h : adm S' ψ),
      C7R4.IsChartAnswer Λ star β pt hQ XU Z ζ ι ptZ S s X t S' ψ (z S' ψ h) :=
    fun S' _ ψ h => (F1 S' ψ h).choose_spec
  have hz : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (hψ : adm S' ψ) (χ : S' →+* S'')
      (hχ : adm S'' (χ.comp ψ)), z S'' (χ.comp ψ) hχ = Spec.map (CommRingCat.ofHom χ) ≫ z S' ψ hψ :=
    fun S' S'' _ _ ψ hψ χ hχ => F2 S'' (χ.comp ψ) _ _ (hzspec S'' _ hχ) (F3 S' S'' ψ χ _ (hzspec S' ψ hψ))

  let R : Set S := {r | adm (Localization.Away r) (algebraMap S (Localization.Away r))}
  have hR : Ideal.span R = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hR𝔪⟩ := Ideal.exists_le_maximal (Ideal.span R) hne
    let x : ↥(Spec (CommRingCat.of S)) := ⟨𝔪, h𝔪.isPrime⟩

    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p.base x)) isOpen_univ
    have hopen : IsOpen (p.base ⁻¹' (U : Set M)) := U.isOpen.preimage p.base.hom.continuous
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open (show x ∈ p.base ⁻¹' (U : Set M) from hxU) hopen
    have hrR : r ∈ R := by
      refine ⟨⟨U, hU⟩, ?_⟩
      rintro _ ⟨y, rfl⟩
      apply hrU
      show (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))).base y ∈
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S))
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨y, rfl⟩
    have : r ∈ 𝔪 := hR𝔪 (Ideal.subset_span hrR)
    exact hxr this
  obtain ⟨q₀, hq₀, -⟩ :=
    AlgebraicGeometry.Spec.exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top adm hadm z hz R hR
      (fun r hr => hr)

  have hover : q₀ ≫ f = p := by
    obtain ⟨qM, -, huniq⟩ :=
      AlgebraicGeometry.Spec.exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top (Y := M) adm hadm
        (fun S' _ ψ _ => Spec.map (CommRingCat.ofHom ψ) ≫ p)
        (fun S' S'' _ _ ψ _ χ _ => by simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]) R hR (fun r hr => hr)
    have e1 : q₀ ≫ f = qM := huniq _ fun r hr => by
      obtain ⟨U, φ, hφ, X', t', hX', ht', X'', hX'', t'', hi, hv⟩ := hzspec _ _ hr
      rw [← Category.assoc, hq₀ _ _ hr, hv, Category.assoc, (hsq U).w, ← Category.assoc,
        (ptZ U _ φ X'' hX'' t'').2, hφ]
    have e2 : p = qM := huniq _ fun r hr => rfl
    rw [e1, ← e2]
  refine ⟨⟨q₀, by rw [← Category.assoc, hover]; exact (pt S s ⟨X, hQ S s X t⟩).2⟩, hover, ?_⟩

  intro S' _ ψ U φ hφ X' t' hX' ht' X'' hX'' t'' hi
  have hψ : adm S' ψ := ⟨U, by
    rw [← hφ]
    rintro _ ⟨y, rfl⟩
    exact U.2.range_fromSpec.subset ⟨_, rfl⟩⟩
  show Spec.map (CommRingCat.ofHom ψ) ≫ q₀ = _
  rw [hq₀ S' ψ hψ]
  exact F2 S' ψ _ _ (hzspec S' ψ hψ) ⟨U, φ, hφ, X', t', hX', ht', X'', hX'', t'', hi, rfl⟩

end S_CerednikDrinfeld_QM_exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_schemeHomOver_forall_comp_eq_ptZ_comp_openImmersion_of_affineCharts_satisfying (solution)
