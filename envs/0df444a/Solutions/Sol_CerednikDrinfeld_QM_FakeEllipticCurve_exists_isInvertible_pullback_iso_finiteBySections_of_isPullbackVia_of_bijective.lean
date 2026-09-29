-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_finiteBySections_of_isPullbackVia_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/4bf2f6b1-6610-59b3-bd6d-7145848a6397

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_finiteBySections_of_isPullbackVia_of_bijective

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (ι : S →+* S') (hι : Function.Bijective ι)
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia ι E E' g)
    (𝓛' : E'.A.Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hfs : Scheme.Modules.FiniteBySections (𝓛' ⊗ 𝓛' ⊗ 𝓛') E'.f) :
    ∃ 𝓛 : E.A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛') ∧
      Scheme.Modules.FiniteBySections (𝓛 ⊗ 𝓛 ⊗ 𝓛) E.f := by
  obtain ⟨hpb, -, -, -⟩ := hg

  haveI : IsIso (CommRingCat.ofHom ι) := (RingEquiv.ofBijective ι hι).toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom ι)) := inferInstance
  haveI : IsIso g := hpb.isIso_fst_of_isIso

  letI alg : Algebra S' S := ((RingEquiv.ofBijective ι hι).symm : S' →+* S).toAlgebra
  have key : ∀ y, ι ((RingEquiv.ofBijective ι hι).symm y) = y := fun y => by
    rw [← RingEquiv.ofBijective_apply ι hι]; exact (RingEquiv.ofBijective ι hι).apply_symm_apply y
  have hιa : ι.comp (algebraMap S' S) = RingHom.id S' := RingHom.ext fun y => key y
  have hSpec : Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom (algebraMap S' S)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hιa, CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (CommRingCat.ofHom (algebraMap S' S)) :=
    (RingEquiv.ofBijective ι hι).symm.toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap S' S))) := inferInstance
  have w : inv g ≫ E'.f = E.f ≫ Spec.map (CommRingCat.ofHom (algebraMap S' S)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hpb.w, Category.assoc, hSpec, Category.comp_id]
  have hsq : IsPullback (inv g) E.f E'.f (Spec.map (CommRingCat.ofHom (algebraMap S' S))) :=
    IsPullback.of_horiz_isIso ⟨w⟩

  set 𝓛 : E.A.Modules := (Scheme.Modules.pullback (inv g)).obj 𝓛' with h𝓛def
  have e : (Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛' :=
    (Scheme.Modules.pullbackComp g (inv g)).app 𝓛' ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id g)).app 𝓛' ≪≫ (Scheme.Modules.pullbackId _).app 𝓛'
  refine ⟨𝓛, Scheme.Modules.IsInvertible.pullback (inv g) h𝓛', ⟨e⟩, ?_⟩
  obtain ⟨Nn, 𝔓, hfin⟩ := hfs
  obtain ⟨𝔓', -, -, hpb'⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback hsq 𝔓
  have hfin' : IsFinite 𝔓'.toProj := MorphismProperty.of_isPullback hpb' hfin

  let e3 : (Scheme.Modules.pullback (inv g)).obj (𝓛' ⊗ 𝓛' ⊗ 𝓛') ≅ 𝓛 ⊗ 𝓛 ⊗ 𝓛 :=
    Scheme.Modules.pullbackTensorObjIso (inv g) _ _ ≪≫
      (Iso.refl _ ⊗ᵢ Scheme.Modules.pullbackTensorObjIso (inv g) _ _)
  obtain ⟨𝔓'', htp, -⟩ := Scheme.Modules.ProjPresentation.exists_of_iso 𝔓' e3
  exact ⟨Nn, 𝔓'', by rw [htp]; exact hfin'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_finiteBySections_of_isPullbackVia_of_bijective
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_finiteBySections_of_isPullbackVia_of_bijective (solution)
