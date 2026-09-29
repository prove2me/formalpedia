-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/50143230-b13d-5dae-abd3-e8d615e625ce

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic
import Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
import Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve QM.FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg QM.FakeEllipticCurve.smoothOfRelativeDimension_two"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt_coe pushPt FactorsThrough nsmulPt geomPoint tangentBase tangentZero tangentScale IsTangentVector FakeEllipticCurve FakeEllipticCurve.IsPullback FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg FakeEllipticCurve.smoothOfRelativeDimension_two"
namespace FakeEllipticCurve
p2m_export "CerednikDrinfeld.QM.FakeEllipticCurve" "Iso IsPullback lev_finite act_trace A f act_hom lev_stable comm act lev_torsion act_one lev_closed L lev_one lev_finitePresentation lev_flat act_mul C lev_rank act_add lev lev_sub lev_fibre dim_fibre act_over bundle exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg smoothOfRelativeDimension_two"
namespace NFDescent
p2m_open "CerednikDrinfeld.QM.FakeEllipticCurve CerednikDrinfeld.QM CerednikDrinfeld"

open scoped Quaternion

section Instances

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

theorem quasiCompact_f (E : FakeEllipticCurve Λ N S) : QuasiCompact E.f := by
  have := E.bundle.proper
  infer_instance

theorem quasiSeparated_f (E : FakeEllipticCurve Λ N S) : QuasiSeparated E.f := by
  have := E.bundle.proper
  infer_instance

theorem locallyOfFiniteType_f (E : FakeEllipticCurve Λ N S) : LocallyOfFiniteType E.f := by
  have := E.bundle.smooth
  infer_instance

theorem compactSpace_A (E : FakeEllipticCurve Λ N S) : CompactSpace E.A := by
  have := quasiCompact_f E
  exact QuasiCompact.compactSpace_of_compactSpace E.f

theorem quasiSeparatedSpace_A (E : FakeEllipticCurve Λ N S) : QuasiSeparatedSpace E.A := by
  have := quasiSeparated_f E
  exact quasiSeparatedSpace_of_quasiSeparated E.f

theorem compactSpace_C (E : FakeEllipticCurve Λ N S) : CompactSpace E.C := by
  have := E.lev_finite
  exact QuasiCompact.compactSpace_of_compactSpace (E.lev ≫ E.f)

theorem quasiSeparatedSpace_C (E : FakeEllipticCurve Λ N S) : QuasiSeparatedSpace E.C := by
  have := E.lev_finite
  exact quasiSeparatedSpace_of_quasiSeparated (E.lev ≫ E.f)

end Instances

section Faithful

theorem flat_specMap_of_field {κ : Type u} [Field κ] {K : Type u} [CommRing K] [Nontrivial K]
    (r : κ →+* K) : Flat (Spec.map (CommRingCat.ofHom r)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  letI := r.toAlgebra
  show Module.Flat κ K
  infer_instance

theorem surjective_specMap_of_field {κ : Type u} [Field κ] {K : Type u} [CommRing K] [Nontrivial K]
    (r : κ →+* K) : Surjective (Spec.map (CommRingCat.ofHom r)) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
  exact ⟨x, Subsingleton.elim _ _⟩

abbrev Fpqc : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact

theorem fpqc_specMap_of_field {κ : Type u} [Field κ] {K : Type u} [CommRing K] [Nontrivial K]
    (r : κ →+* K) : Fpqc (Spec.map (CommRingCat.ofHom r)) :=
  ⟨⟨surjective_specMap_of_field r, flat_specMap_of_field r⟩, inferInstance⟩

theorem fpqc_of_isPullback_specMap_of_field {κ : Type u} [Field κ] {K : Type u} [CommRing K] [Nontrivial K]
    (r : κ →+* K) {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} {f₀ : X₀ ⟶ Spec (CommRingCat.of κ)}
    {g : X ⟶ X₀} (hg : CategoryTheory.IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom r))) : Fpqc g :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hg.flip (surjective_specMap_of_field r),
    MorphismProperty.of_isPullback (P := @Flat) hg.flip (flat_specMap_of_field r)⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) hg.flip inferInstance⟩

theorem epi_of_fpqc {X Y : Scheme.{u}} {g : X ⟶ Y} (hg : Fpqc g) : Epi g := by
  obtain ⟨⟨h₁, h₂⟩, _⟩ := hg
  exact Flat.epi_of_flat_of_surjective g

theorem epi_of_isPullback_specMap_of_field {κ : Type u} [Field κ] {K : Type u} [CommRing K] [Nontrivial K]
    (r : κ →+* K) {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} {f₀ : X₀ ⟶ Spec (CommRingCat.of κ)}
    {g : X ⟶ X₀} (hg : CategoryTheory.IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom r))) : Epi g :=
  epi_of_fpqc (fpqc_of_isPullback_specMap_of_field r hg)

end Faithful

section Descent

theorem isClosedImmersion_descendsAlong :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u}) Fpqc := by
  have h₁ := AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have h₂ := AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have h₃ : (MorphismProperty.monomorphisms Scheme.{u}).DescendsAlong Fpqc := by
    rw [← MorphismProperty.diagonal_isomorphisms]
    infer_instance
  rw [IsClosedImmersion.eq_isFinite_inf_mono, IsFinite.eq_isProper_inf_isAffineHom]
  infer_instance

theorem isFinite_descendsAlong :
    MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{u}) Fpqc := by
  have h₁ := AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have h₂ := AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  rw [IsFinite.eq_isProper_inf_isAffineHom]
  infer_instance

theorem exists_comp_eq_of_exists_comp_eq_comp {C X T T' : Scheme.{u}} (m : C ⟶ X) [Mono m] (P : T ⟶ X)
    (pr : T' ⟶ T) (hpr : Fpqc pr) (h : ∃ Q : T' ⟶ C, Q ≫ m = pr ≫ P) : ∃ P₀ : T ⟶ C, P₀ ≫ m = P := by
  obtain ⟨Q, hQ⟩ := h
  let m' := pullback.snd m P
  let s₁ : T' ⟶ pullback m P := pullback.lift Q pr hQ
  have hs₁ : s₁ ≫ m' = pr := pullback.lift_snd _ _ _
  let m'' := pullback.snd m' pr
  let s : T' ⟶ pullback m' pr := pullback.lift s₁ (𝟙 T') (by rw [hs₁, Category.id_comp])
  have hs : s ≫ m'' = 𝟙 T' := pullback.lift_snd _ _ _
  have : IsSplitEpi m'' := IsSplitEpi.mk' ⟨s, hs⟩
  have : Mono m'' := inferInstance
  have hiso'' : IsIso m'' := isIso_of_mono_of_isSplitEpi m''
  have hiso' : IsIso m' :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{u}) (Q := Fpqc)
      (CategoryTheory.IsPullback.of_hasPullback m' pr).flip hpr hiso''
  refine ⟨inv m' ≫ pullback.fst m P, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end Descent

section GeometricPoints

theorem exists_ringHom_comp_algebraMap_eq (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {k : Type u} [Field k] [IsAlgClosed k] (sk : K →+* k) :
    ∃ σ : AlgebraicClosure ℚ →+* k, σ.comp (algebraMap K (AlgebraicClosure ℚ)) = sk := by
  letI : Algebra K k := sk.toAlgebra
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := IntermediateField.isAlgebraic_tower_top
  refine ⟨(IsAlgClosed.lift (R := K) (M := k) (S := AlgebraicClosure ℚ)).toRingHom, ?_⟩
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes]
  rfl

end GeometricPoints

section Relevel

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

abbrev ιK (L : IntermediateField k K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L K))

abbrev ιLL' {L L' : IntermediateField k K} (h : L ≤ L') : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

theorem ιK_comp_ιLL' {L L' : IntermediateField k K} (h : L ≤ L') : ιK L' ≫ ιLL' h = ιK L := by
  simp only [ιK, ιLL', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_relevel {L L' : IntermediateField k K} (h : L ≤ L') {X X₀ : Scheme.{u}}
    {fX : X ⟶ Spec (CommRingCat.of K)} {f₀ : X₀ ⟶ Spec (CommRingCat.of L)} {g : X ⟶ X₀}
    (hg : CategoryTheory.IsPullback g fX f₀ (ιK L)) :
    ∃ (g' : X ⟶ pullback f₀ (ιLL' h)),
      CategoryTheory.IsPullback g' fX (pullback.snd f₀ (ιLL' h)) (ιK L') ∧ g' ≫ pullback.fst f₀ (ιLL' h) = g := by
  have hw : g ≫ f₀ = (fX ≫ ιK L') ≫ ιLL' h := by rw [Category.assoc, ιK_comp_ιLL', hg.w]
  refine ⟨pullback.lift g (fX ≫ ιK L') hw, ?_, pullback.lift_fst _ _ _⟩
  refine CategoryTheory.IsPullback.of_right (h₁₂ := pullback.fst f₀ (ιLL' h)) (h₂₂ := ιLL' h) ?_ (pullback.lift_snd _ _ _)
    (CategoryTheory.IsPullback.of_hasPullback f₀ (ιLL' h))
  rw [pullback.lift_fst, ιK_comp_ιLL']
  exact hg

theorem compactSpace_relevel {L L' : IntermediateField k K} (h : L ≤ L') {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of L)) [CompactSpace X₀] : CompactSpace ↥(pullback f₀ (ιLL' h)) := by
  have : QuasiCompact f₀ := (quasiCompact_iff_compactSpace f₀).mpr ‹_›
  infer_instance

theorem quasiSeparatedSpace_relevel {L L' : IntermediateField k K} (h : L ≤ L') {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of L)) [QuasiSeparatedSpace X₀] :
    QuasiSeparatedSpace ↥(pullback f₀ (ιLL' h)) := by
  have : QuasiSeparated f₀ := QuasiSeparated.of_quasiSeparatedSpace f₀
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd f₀ (ιLL' h))

end Relevel

section MorSpread

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_relevel_hom_comp_eq [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k L] {C X C₀ X₀ : Scheme.{0}}
    {fC : C ⟶ Spec (CommRingCat.of K)} {fX : X ⟶ Spec (CommRingCat.of K)}
    {c₀ : C₀ ⟶ Spec (CommRingCat.of L)} {f₀ : X₀ ⟶ Spec (CommRingCat.of L)}
    [CompactSpace C₀] [QuasiSeparatedSpace C₀] [LocallyOfFiniteType f₀]
    {gC : C ⟶ C₀} (hgC : CategoryTheory.IsPullback gC fC c₀ (ιK L))
    {g : X ⟶ X₀} (hg : CategoryTheory.IsPullback g fX f₀ (ιK L)) (φ : C ⟶ X) (hφ : φ ≫ fX = fC) :
    ∃ (L' : IntermediateField k K) (_ : FiniteDimensional k L') (h : L ≤ L')
      (gC' : C ⟶ pullback c₀ (ιLL' h)) (_ : CategoryTheory.IsPullback gC' fC (pullback.snd c₀ (ιLL' h)) (ιK L'))
      (_ : gC' ≫ pullback.fst c₀ (ιLL' h) = gC)
      (g' : X ⟶ pullback f₀ (ιLL' h)) (_ : CategoryTheory.IsPullback g' fX (pullback.snd f₀ (ιLL' h)) (ιK L'))
      (_ : g' ≫ pullback.fst f₀ (ιLL' h) = g)
      (φ₀ : pullback c₀ (ιLL' h) ⟶ pullback f₀ (ιLL' h)),
      φ₀ ≫ pullback.snd f₀ (ιLL' h) = pullback.snd c₀ (ιLL' h) ∧ φ ≫ g' = gC' ≫ φ₀ := by

  let eC := hgC.isoPullback
  let eX := hg.isoPullback
  have heC_fst : eC.hom ≫ pullback.fst c₀ (ιK L) = gC := hgC.isoPullback_hom_fst
  have heC_snd : eC.hom ≫ pullback.snd c₀ (ιK L) = fC := hgC.isoPullback_hom_snd
  have heCi_snd : eC.inv ≫ fC = pullback.snd c₀ (ιK L) := hgC.isoPullback_inv_snd
  have heX_fst : eX.hom ≫ pullback.fst f₀ (ιK L) = g := hg.isoPullback_hom_fst
  have heX_snd : eX.hom ≫ pullback.snd f₀ (ιK L) = fX := hg.isoPullback_hom_snd
  let ψ := eC.inv ≫ φ ≫ eX.hom
  have hψ : ψ ≫ pullback.snd f₀ (ιK L) = pullback.snd c₀ (ιK L) := by
    simp only [ψ, Category.assoc, heX_snd, hφ, heCi_snd]
  have : Algebra.IsAlgebraic (↥L) K := IntermediateField.isAlgebraic_tower_top
  obtain ⟨L₂, fin₂, γ, hι₂, hγs, hγsq⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
      (↥L) K C₀ X₀ c₀ f₀ ψ hψ

  let L' : IntermediateField k K := L₂.restrictScalars k
  have hfin' : FiniteDimensional k L' := by
    have : FiniteDimensional k L₂ := FiniteDimensional.trans k (↥L) (↥L₂)
    exact this
  have h : L ≤ L' := fun x hx => by
    change x ∈ L₂
    simpa using L₂.algebraMap_mem ⟨x, hx⟩
  let ι₁₂ : Spec (CommRingCat.of ↥L₂) ⟶ Spec (CommRingCat.of ↥L) := Spec.map (CommRingCat.ofHom (algebraMap (↥L) (↥L₂)))
  have hι₁₂ : ι₁₂ = ιLL' h := rfl
  let ιK₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥L₂) := Spec.map (CommRingCat.ofHom (algebraMap (↥L₂) K))
  have hιK₂ : ιK₂ = ιK L' := rfl
  have hbot : ιK₂ ≫ ι₁₂ = ιK L := hι₂

  let pmX : pullback f₀ (ιK L) ⟶ pullback f₀ ι₁₂ :=
    pullback.map f₀ (Spec.map (CommRingCat.ofHom (algebraMap (↥L) K))) f₀ ι₁₂ (𝟙 X₀) ιK₂ (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι₂])
  let pmC : pullback c₀ (ιK L) ⟶ pullback c₀ ι₁₂ :=
    pullback.map c₀ (Spec.map (CommRingCat.ofHom (algebraMap (↥L) K))) c₀ ι₁₂ (𝟙 C₀) ιK₂ (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι₂])
  have hpmX_fst : pmX ≫ pullback.fst f₀ ι₁₂ = pullback.fst f₀ (ιK L) := by
    simp only [pmX, pullback.lift_fst, Category.comp_id]
  have hpmX_snd : pmX ≫ pullback.snd f₀ ι₁₂ = pullback.snd f₀ (ιK L) ≫ ιK₂ := by
    simp only [pmX, pullback.lift_snd]
  have hpmC_fst : pmC ≫ pullback.fst c₀ ι₁₂ = pullback.fst c₀ (ιK L) := by
    simp only [pmC, pullback.lift_fst, Category.comp_id]
  have hpmC_snd : pmC ≫ pullback.snd c₀ ι₁₂ = pullback.snd c₀ (ιK L) ≫ ιK₂ := by
    simp only [pmC, pullback.lift_snd]
  have hpmX : CategoryTheory.IsPullback pmX (pullback.snd f₀ (ιK L)) (pullback.snd f₀ ι₁₂) ιK₂ := by
    have s : CategoryTheory.IsPullback (pmX ≫ pullback.fst f₀ ι₁₂) (pullback.snd f₀ (ιK L)) f₀ (ιK₂ ≫ ι₁₂) := by
      rw [hpmX_fst, hbot]
      exact CategoryTheory.IsPullback.of_hasPullback f₀ (ιK L)
    exact CategoryTheory.IsPullback.of_right s hpmX_snd (CategoryTheory.IsPullback.of_hasPullback f₀ ι₁₂)
  have hpmC : CategoryTheory.IsPullback pmC (pullback.snd c₀ (ιK L)) (pullback.snd c₀ ι₁₂) ιK₂ := by
    have s : CategoryTheory.IsPullback (pmC ≫ pullback.fst c₀ ι₁₂) (pullback.snd c₀ (ιK L)) c₀ (ιK₂ ≫ ι₁₂) := by
      rw [hpmC_fst, hbot]
      exact CategoryTheory.IsPullback.of_hasPullback c₀ (ιK L)
    exact CategoryTheory.IsPullback.of_right s hpmC_snd (CategoryTheory.IsPullback.of_hasPullback c₀ ι₁₂)
  have heXsq : CategoryTheory.IsPullback eX.hom fX (pullback.snd f₀ (ιK L)) (𝟙 _) :=
    CategoryTheory.IsPullback.of_horiz_isIso ⟨by rw [heX_snd, Category.comp_id]⟩
  have heCsq : CategoryTheory.IsPullback eC.hom fC (pullback.snd c₀ (ιK L)) (𝟙 _) :=
    CategoryTheory.IsPullback.of_horiz_isIso ⟨by rw [heC_snd, Category.comp_id]⟩
  have hg' : CategoryTheory.IsPullback (eX.hom ≫ pmX) fX (pullback.snd f₀ ι₁₂) (ιK L') := by
    have := heXsq.paste_horiz hpmX
    rwa [Category.id_comp] at this
  have hgC' : CategoryTheory.IsPullback (eC.hom ≫ pmC) fC (pullback.snd c₀ ι₁₂) (ιK L') := by
    have := heCsq.paste_horiz hpmC
    rwa [Category.id_comp] at this
  refine ⟨L', hfin', h, eC.hom ≫ pmC, hgC', ?_, eX.hom ≫ pmX, hg', ?_, γ, hγs, ?_⟩
  · show eC.hom ≫ pmC ≫ pullback.fst c₀ ι₁₂ = gC
    rw [hpmC_fst, heC_fst]
  · show eX.hom ≫ pmX ≫ pullback.fst f₀ ι₁₂ = g
    rw [hpmX_fst, heX_fst]
  · have hφe : φ ≫ eX.hom = eC.hom ≫ ψ := by simp only [ψ, Iso.hom_inv_id_assoc]
    have hγsq' : ψ ≫ pmX = pmC ≫ γ := hγsq
    show φ ≫ eX.hom ≫ pmX = (eC.hom ≫ pmC) ≫ γ
    rw [← Category.assoc, hφe, Category.assoc, hγsq', Category.assoc]

end MorSpread

section Along

variable {R₀ R : Type u} [CommRing R₀] [CommRing R] (φ : R₀ →+* R)
  {X₀ X : Scheme.{u}} {f₀ : X₀ ⟶ Spec (CommRingCat.of R₀)} {fX : X ⟶ Spec (CommRingCat.of R)}
  (L₀ : RelativeGroupLaw R₀ f₀) (LX : RelativeGroupLaw R fX)
  (g : X ⟶ X₀) (hg : CategoryTheory.IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom φ)))

structure IsHomAlong : Prop where
  mul_comp : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' fX),
    (LX.mul t' P Q).1 ≫ g =
      (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

variable {φ L₀ LX g hg}

theorem nsmulPt_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x) =
      L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x)
    rw [L.mul_natural, ih]

theorem inv_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  have h' : (schemeHomOverComp ψ hψ (L.inv t x)) * (schemeHomOverComp ψ hψ x) = 1 := h
  exact eq_inv_of_mul_eq_one_left h'

section PointsOverExtendedBase

variable {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R)} {t : T ⟶ Spec (CommRingCat.of R₀)}
  (ht : t' ≫ Spec.map (CommRingCat.ofHom φ) = t)

def alongEquiv : SchemeHomOver t' fX ≃ SchemeHomOver t f₀ where
  toFun P := ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2, ht]⟩
  invFun Q := ⟨hg.lift Q.1 t' (by rw [Q.2, ht]), hg.lift_snd _ _ _⟩
  left_inv P := Subtype.ext (hg.hom_ext (by simp only [IsPullback.lift_fst]) (by simp only [IsPullback.lift_snd, P.2]))
  right_inv Q := Subtype.ext (hg.lift_fst _ _ _)

@[scoped simp] theorem alongEquiv_coe (P : SchemeHomOver t' fX) : (alongEquiv (hg := hg) ht P).1 = P.1 ≫ g := rfl

theorem alongEquiv_symm_comp (Q : SchemeHomOver t f₀) : ((alongEquiv (hg := hg) ht).symm Q).1 ≫ g = Q.1 :=
  hg.lift_fst _ _ _

theorem alongEquiv_mul (hgm : IsHomAlong φ L₀ LX g hg) (P Q : SchemeHomOver t' fX) :
    alongEquiv (hg := hg) ht (LX.mul t' P Q) =
      L₀.mul t (alongEquiv (hg := hg) ht P) (alongEquiv (hg := hg) ht Q) := by
  subst ht
  exact Subtype.ext (hgm.mul_comp t' P Q)

theorem alongEquiv_one (hgm : IsHomAlong φ L₀ LX g hg) : alongEquiv (hg := hg) ht (LX.one t') = L₀.one t := by
  letI := L₀.pointGroup t
  have h := alongEquiv_mul ht hgm (LX.one t') (LX.one t')
  rw [LX.one_mul] at h
  exact mul_eq_left.mp h.symm

theorem alongEquiv_inv (hgm : IsHomAlong φ L₀ LX g hg) (P : SchemeHomOver t' fX) :
    alongEquiv (hg := hg) ht (LX.inv t' P) = L₀.inv t (alongEquiv (hg := hg) ht P) := by
  letI := L₀.pointGroup t
  have h := alongEquiv_mul ht hgm (LX.inv t' P) P
  rw [LX.inv_mul_cancel, alongEquiv_one ht hgm] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem alongEquiv_nsmul (hgm : IsHomAlong φ L₀ LX g hg) (n : ℕ) (P : SchemeHomOver t' fX) :
    alongEquiv (hg := hg) ht (nsmulPt LX t' n P) = nsmulPt L₀ t n (alongEquiv (hg := hg) ht P) := by
  induction n with
  | zero => exact alongEquiv_one ht hgm
  | succ n ih =>
    show alongEquiv (hg := hg) ht (LX.mul t' (nsmulPt LX t' n P) P) =
      L₀.mul t (nsmulPt L₀ t n (alongEquiv (hg := hg) ht P)) (alongEquiv (hg := hg) ht P)
    rw [alongEquiv_mul ht hgm, ih]

theorem alongEquiv_pushPt {u : X ⟶ X} (hu : u ≫ fX = fX) {u₀ : X₀ ⟶ X₀} (hu₀ : u₀ ≫ f₀ = f₀)
    (huu : u ≫ g = g ≫ u₀) (P : SchemeHomOver t' fX) :
    alongEquiv (hg := hg) ht (pushPt u hu P) = pushPt u₀ hu₀ (alongEquiv (hg := hg) ht P) := by
  apply Subtype.ext
  simp only [alongEquiv_coe, mapPt_coe, Category.assoc, huu]

theorem factorsThrough_alongEquiv_iff {C₀ C : Scheme.{u}} {lev₀ : C₀ ⟶ X₀} {lev : C ⟶ X} {gC : C ⟶ C₀}
    (hC : CategoryTheory.IsPullback lev gC g lev₀) (P : SchemeHomOver t' fX) :
    FactorsThrough lev₀ (alongEquiv (hg := hg) ht P) ↔ FactorsThrough lev P := by
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    refine ⟨hC.lift P.1 Q₀ (by simpa using hQ₀.symm), hC.lift_fst _ _ _⟩
  · rintro ⟨P₀, hP₀⟩
    refine ⟨P₀ ≫ gC, ?_⟩
    simp only [alongEquiv_coe, Category.assoc, ← hC.w, ← hP₀]

end PointsOverExtendedBase

section BaseChangeOfTestObjects

variable (hfp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)), Fpqc (pullback.fst t (Spec.map (CommRingCat.ofHom φ))))

def liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (P : SchemeHomOver t f₀) :
    SchemeHomOver (pullback.snd t (Spec.map (CommRingCat.ofHom φ))) fX :=
  (alongEquiv (hg := hg) (t := pullback.fst t (Spec.map (CommRingCat.ofHom φ)) ≫ t) pullback.condition.symm).symm
    (schemeHomOverComp (pullback.fst t (Spec.map (CommRingCat.ofHom φ))) rfl P)

theorem alongEquiv_liftPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (P : SchemeHomOver t f₀) :
    alongEquiv (hg := hg) pullback.condition.symm (liftPt (hg := hg) P) =
      schemeHomOverComp (pullback.fst t (Spec.map (CommRingCat.ofHom φ))) rfl P :=
  Equiv.apply_symm_apply _ _

theorem liftPt_comp {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (P : SchemeHomOver t f₀) :
    (liftPt (hg := hg) P).1 ≫ g = pullback.fst t (Spec.map (CommRingCat.ofHom φ)) ≫ P.1 :=
  congrArg Subtype.val (alongEquiv_liftPt (hg := hg) P)

include hfp in
theorem liftPt_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} :
    Function.Injective (liftPt (hg := hg) (t := t)) := by
  intro P Q h
  have h' := congrArg (fun S => S.1 ≫ g) h
  simp only [liftPt_comp] at h'
  have := epi_of_fpqc (hfp t)
  exact Subtype.ext ((cancel_epi _).mp h')

theorem liftPt_mul (hgm : IsHomAlong φ L₀ LX g hg) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)}
    (P Q : SchemeHomOver t f₀) :
    liftPt (hg := hg) (L₀.mul t P Q) = LX.mul _ (liftPt (hg := hg) P) (liftPt (hg := hg) Q) := by
  apply (alongEquiv (hg := hg) (pullback.condition (f := t) (g := Spec.map (CommRingCat.ofHom φ))).symm).injective
  rw [alongEquiv_mul _ hgm, alongEquiv_liftPt, alongEquiv_liftPt, alongEquiv_liftPt, L₀.mul_natural]

theorem liftPt_one (hgm : IsHomAlong φ L₀ LX g hg) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)) :
    liftPt (hg := hg) (L₀.one t) = LX.one _ := by
  apply (alongEquiv (hg := hg) (pullback.condition (f := t) (g := Spec.map (CommRingCat.ofHom φ))).symm).injective
  rw [alongEquiv_one _ hgm, alongEquiv_liftPt, L₀.one_natural]

theorem liftPt_inv (hgm : IsHomAlong φ L₀ LX g hg) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)}
    (P : SchemeHomOver t f₀) :
    liftPt (hg := hg) (L₀.inv t P) = LX.inv _ (liftPt (hg := hg) P) := by
  apply (alongEquiv (hg := hg) (pullback.condition (f := t) (g := Spec.map (CommRingCat.ofHom φ))).symm).injective
  rw [alongEquiv_inv _ hgm, alongEquiv_liftPt, alongEquiv_liftPt, inv_natural]

theorem liftPt_nsmul (hgm : IsHomAlong φ L₀ LX g hg) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)}
    (n : ℕ) (P : SchemeHomOver t f₀) :
    liftPt (hg := hg) (nsmulPt L₀ t n P) = nsmulPt LX _ n (liftPt (hg := hg) P) := by
  apply (alongEquiv (hg := hg) (pullback.condition (f := t) (g := Spec.map (CommRingCat.ofHom φ))).symm).injective
  rw [alongEquiv_nsmul _ hgm, alongEquiv_liftPt, alongEquiv_liftPt, nsmulPt_natural]

theorem liftPt_pushPt {u : X ⟶ X} (hu : u ≫ fX = fX) {u₀ : X₀ ⟶ X₀} (hu₀ : u₀ ≫ f₀ = f₀)
    (huu : u ≫ g = g ≫ u₀) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (P : SchemeHomOver t f₀) :
    liftPt (hg := hg) (pushPt u₀ hu₀ P) = pushPt u hu (liftPt (hg := hg) P) := by
  apply (alongEquiv (hg := hg) (pullback.condition (f := t) (g := Spec.map (CommRingCat.ofHom φ))).symm).injective
  rw [alongEquiv_pushPt _ hu hu₀ huu, alongEquiv_liftPt, alongEquiv_liftPt]
  rfl

theorem factorsThrough_iff_factorsThrough_liftPt {C₀ C : Scheme.{u}} {lev₀ : C₀ ⟶ X₀} [Mono lev₀] {lev : C ⟶ X}
    {gC : C ⟶ C₀} (hC : CategoryTheory.IsPullback lev gC g lev₀)
    (hfp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₀)), Fpqc (pullback.fst t (Spec.map (CommRingCat.ofHom φ))))
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R₀)} (P : SchemeHomOver t f₀) :
    FactorsThrough lev₀ P ↔ FactorsThrough lev (liftPt (hg := hg) P) := by
  rw [← factorsThrough_alongEquiv_iff (hg := hg) pullback.condition.symm hC, alongEquiv_liftPt]
  constructor
  · rintro ⟨P₀, hP₀⟩
    exact ⟨pullback.fst t (Spec.map (CommRingCat.ofHom φ)) ≫ P₀, by simp only [Category.assoc, hP₀, schemeHomOverComp_coe]⟩
  · rintro ⟨Q, hQ⟩
    exact exists_comp_eq_of_exists_comp_eq_comp lev₀ P.1 _ (hfp t) ⟨Q, hQ⟩

end BaseChangeOfTestObjects

end Along

section GeomTransfer

variable {R₀ R : Type u} [CommRing R₀] [CommRing R] {φ : R₀ →+* R}
  {X₀ X : Scheme.{u}} {f₀ : X₀ ⟶ Spec (CommRingCat.of R₀)} {fX : X ⟶ Spec (CommRingCat.of R)}
  {L₀ : RelativeGroupLaw R₀ f₀} {LX : RelativeGroupLaw R fX}
  {g : X ⟶ X₀} {hg : CategoryTheory.IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom φ))}

theorem geomPoint_comp (k : Type u) [Field k] (σ : R →+* k) :
    geomPoint k σ ≫ Spec.map (CommRingCat.ofHom φ) = geomPoint k (σ.comp φ) := by
  simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem tangentBase_comp (k : Type u) [Field k] (σ : R →+* k) :
    tangentBase k σ ≫ Spec.map (CommRingCat.ofHom φ) = tangentBase k (σ.comp φ) := by
  simp only [tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]

theorem tangentZero_comp_tangentBase {S : Type u} [CommRing S] (k : Type u) [Field k] (sk : S →+* k) :
    tangentZero k ≫ tangentBase k sk = geomPoint k sk := by
  have h : (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((algebraMap k (DualNumber k)).comp sk) = sk := by
    rw [← RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact RingHom.id_comp sk
  simp only [tangentZero, tangentBase, geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tangentScale_comp_tangentBase {S : Type u} [CommRing S] (k : Type u) [Field k] (sk : S →+* k) (c : k) :
    tangentScale k c ≫ tangentBase k sk = tangentBase k sk := by
  have h : (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom.comp
      ((algebraMap k (DualNumber k)).comp sk) = (algebraMap k (DualNumber k)).comp sk := by
    rw [← RingHom.comp_assoc, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
  simp only [tangentScale, tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem isTangentVector_alongEquiv_iff (hgm : IsHomAlong φ L₀ LX g hg) (k : Type u) [Field k] (σ : R →+* k)
    (P : SchemeHomOver (tangentBase k σ) fX) :
    IsTangentVector L₀ k (σ.comp φ) (alongEquiv (hg := hg) (tangentBase_comp k σ) P) ↔ IsTangentVector LX k σ P := by
  unfold IsTangentVector
  have hone := congrArg Subtype.val (alongEquiv_one (hg := hg) (geomPoint_comp k σ) hgm)
  simp only [alongEquiv_coe] at hone
  rw [alongEquiv_coe, ← hone, ← Category.assoc]
  constructor
  · intro h
    apply hg.hom_ext h
    rw [Category.assoc, P.2, (LX.one (geomPoint k σ)).2, tangentZero_comp_tangentBase]
  · intro h
    rw [h]

theorem trace_transfer (hgm : IsHomAlong φ L₀ LX g hg) (k : Type u) [Field k] (σ : R →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k (σ.comp φ)) f₀)
    (hτi : Function.Injective τ)
    (hτr : ∀ P : SchemeHomOver (tangentBase k (σ.comp φ)) f₀, P ∈ Set.range τ ↔ IsTangentVector L₀ k (σ.comp φ) P)
    (hτa : ∀ v w : V, τ (v + w) = L₀.mul (tangentBase k (σ.comp φ)) (τ v) (τ w))
    (hτs : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    {u : X ⟶ X} (hu : u ≫ fX = fX) {u₀ : X₀ ⟶ X₀} (hu₀ : u₀ ≫ f₀ = f₀) (huu : u ≫ g = g ≫ u₀)
    (Φ : V →ₗ[k] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt u₀ hu₀ (τ v)) :
    ∃ τ' : V → SchemeHomOver (tangentBase k σ) fX,
      Function.Injective τ' ∧
      (∀ P : SchemeHomOver (tangentBase k σ) fX, P ∈ Set.range τ' ↔ IsTangentVector LX k σ P) ∧
      (∀ v w : V, τ' (v + w) = LX.mul (tangentBase k σ) (τ' v) (τ' w)) ∧
      (∀ (c : k) (v : V), (τ' (c • v)).1 = tangentScale k c ≫ (τ' v).1) ∧
      (∀ v : V, τ' (Φ v) = pushPt u hu (τ' v)) := by
  let e := alongEquiv (hg := hg) (fX := fX) (f₀ := f₀) (tangentBase_comp k σ)
  refine ⟨fun v => e.symm (τ v), ?_, ?_, ?_, ?_, ?_⟩
  · exact e.symm.injective.comp hτi
  · intro P
    rw [← isTangentVector_alongEquiv_iff hgm, ← hτr]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, by rw [← hv]; exact (e.apply_symm_apply _).symm⟩
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      show e.symm (τ v) = P
      rw [hv]
      exact e.symm_apply_apply _
  · intro v w
    apply e.injective
    rw [alongEquiv_mul _ hgm]
    simp only [e, Equiv.apply_symm_apply, hτa]
  · intro c v
    apply hg.hom_ext
    · rw [alongEquiv_symm_comp, Category.assoc, alongEquiv_symm_comp, hτs]
    · rw [(e.symm (τ (c • v))).2, Category.assoc, (e.symm (τ v)).2, tangentScale_comp_tangentBase]
  · intro v
    apply e.injective
    rw [alongEquiv_pushPt _ hu hu₀ huu]
    simp only [e, Equiv.apply_symm_apply, hΦ]

theorem levFibre_transfer (hgm : IsHomAlong φ L₀ LX g hg) {C₀ C : Scheme.{u}} {lev₀ : C₀ ⟶ X₀} {lev : C ⟶ X}
    {gC : C ⟶ C₀} (hC : CategoryTheory.IsPullback lev gC g lev₀) (k : Type u) [Field k] (σ : R →+* k) {M : Type*} [Add M]
    (e : M ≃ {P : SchemeHomOver (geomPoint k σ) fX // FactorsThrough lev P})
    (he : ∀ x y : M, (e (x + y) : SchemeHomOver (geomPoint k σ) fX) = LX.mul (geomPoint k σ) (e x) (e y)) :
    ∃ e₀ : M ≃ {P : SchemeHomOver (geomPoint k (σ.comp φ)) f₀ // FactorsThrough lev₀ P},
      ∀ x y : M, (e₀ (x + y) : SchemeHomOver (geomPoint k (σ.comp φ)) f₀) = L₀.mul (geomPoint k (σ.comp φ)) (e₀ x) (e₀ y) := by
  let a := alongEquiv (hg := hg) (fX := fX) (f₀ := f₀) (geomPoint_comp k σ)
  let Θ : {P : SchemeHomOver (geomPoint k σ) fX // FactorsThrough lev P} ≃
      {P : SchemeHomOver (geomPoint k (σ.comp φ)) f₀ // FactorsThrough lev₀ P} :=
    a.subtypeEquiv (fun P => (factorsThrough_alongEquiv_iff (geomPoint_comp k σ) hC P).symm)
  refine ⟨e.trans Θ, fun x y => ?_⟩
  show a (e (x + y)).1 = L₀.mul _ (a (e x).1) (a (e y).1)
  rw [he, alongEquiv_mul _ hgm]

end GeomTransfer

section Topology

variable {κ : Type u} [Field κ] {K : Type u} [Field K] (r : κ →+* K)
  {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} {f₀ : X₀ ⟶ Spec (CommRingCat.of κ)}
  {g : X ⟶ X₀} (hg : CategoryTheory.IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom r)))

theorem preimage_singleton_eq_univ_of_field {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ))
    (s : ↥(Spec (CommRingCat.of κ))) : f.base ⁻¹' {s} = Set.univ := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

theorem connectedSpace_of_forall_isConnected_preimage {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of K))
    (h : ∀ s : ↥(Spec (CommRingCat.of K)), _root_.IsConnected (f.base ⁻¹' {s})) : ConnectedSpace Y := by
  have := h default
  rw [preimage_singleton_eq_univ_of_field] at this
  exact connectedSpace_iff_univ.mpr this

include hg in
theorem connectedSpace_of_isPullback [ConnectedSpace X] : ConnectedSpace X₀ := by
  have hs : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) hg.flip (surjective_specMap_of_field r)
  exact hs.1.connectedSpace g.continuous

theorem isConnected_preimage_of_connectedSpace {Y : Scheme.{u}} [ConnectedSpace Y] (f : Y ⟶ Spec (CommRingCat.of κ))
    (s : ↥(Spec (CommRingCat.of κ))) : _root_.IsConnected (f.base ⁻¹' {s}) := by
  rw [preimage_singleton_eq_univ_of_field]
  exact isConnected_univ

theorem topologicalKrullDim_preimage_eq {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ))
    (s : ↥(Spec (CommRingCat.of κ))) : topologicalKrullDim ↥(f.base ⁻¹' {s}) = topologicalKrullDim Y := by
  rw [preimage_singleton_eq_univ_of_field]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph

theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {Y : Scheme.{u}} [Nonempty Y] (f : Y ⟶ Spec (CommRingCat.of κ))
    (n : ℕ) [SmoothOfRelativeDimension n f] : topologicalKrullDim Y = n :=
  le_antisymm (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f n)
    (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim f n)

include hg in

theorem smoothOfRelativeDimension_of_isPullback (n : ℕ) [SmoothOfRelativeDimension n fX] :
    SmoothOfRelativeDimension n f₀ :=
  haveI := AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u} n
  MorphismProperty.of_isPullback_of_descendsAlong (P := @SmoothOfRelativeDimension n) (Q := Fpqc) hg.flip
    (fpqc_specMap_of_field r) ‹_›

include hg in
theorem smooth_of_isPullback [Smooth fX] : Smooth f₀ :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := Fpqc) hg.flip (fpqc_specMap_of_field r) ‹_›

include hg in
theorem isProper_of_isPullback [IsProper fX] : IsProper f₀ :=
  haveI := AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper) (Q := Fpqc) hg.flip (fpqc_specMap_of_field r) ‹_›

include hg in
theorem isFinite_of_isPullback [IsFinite fX] : IsFinite f₀ :=
  haveI := isFinite_descendsAlong.{u}
  MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite) (Q := Fpqc) hg.flip (fpqc_specMap_of_field r) ‹_›

include hg in
theorem locallyOfFinitePresentation_of_isPullback [LocallyOfFinitePresentation fX] : LocallyOfFinitePresentation f₀ :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation) (Q := Fpqc) hg.flip
    (fpqc_specMap_of_field r) ‹_›

end Topology

section Main

variable {a b : ℚ}

theorem exists_numberField_model (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : Λ.FG) (N : ℕ)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (E₀ : FakeEllipticCurve Λ N K),
      FakeEllipticCurve.IsPullback (algebraMap K (AlgebraicClosure ℚ)) E₀ E := by
  have halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI := compactSpace_A E
  haveI := quasiSeparatedSpace_A E
  haveI := locallyOfFiniteType_f E
  haveI := compactSpace_C E
  haveI := quasiSeparatedSpace_C E
  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  haveI : LocallyOfFiniteType (E.lev ≫ E.f) := inferInstance

  obtain ⟨LA, finA, XA, fA₀, csA, qsA, lftA, gA, hgA⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic ℚ (AlgebraicClosure ℚ) E.A E.f
  obtain ⟨LC, finC, XC, fC₀, csC, qsC, lftC, gC, hgC⟩ :=
    AlgebraicGeometry.exists_intermediateField_finiteDimensional_isPullback_of_isAlgebraic ℚ (AlgebraicClosure ℚ) E.C
      (E.lev ≫ E.f)

  haveI := finA
  haveI := finC
  haveI := csA
  haveI := qsA
  haveI := lftA
  haveI := csC
  haveI := qsC
  haveI : FiniteDimensional ℚ ↥(LA ⊔ LC) := IntermediateField.finiteDimensional_sup LA LC
  obtain ⟨gA₁, hgA₁, -⟩ := exists_relevel (le_sup_left : LA ≤ LA ⊔ LC) hgA
  obtain ⟨gC₁, hgC₁, -⟩ := exists_relevel (le_sup_right : LC ≤ LA ⊔ LC) hgC
  haveI := compactSpace_relevel (le_sup_left : LA ≤ LA ⊔ LC) fA₀
  haveI := quasiSeparatedSpace_relevel (le_sup_left : LA ≤ LA ⊔ LC) fA₀
  haveI := compactSpace_relevel (le_sup_right : LC ≤ LA ⊔ LC) fC₀
  haveI := quasiSeparatedSpace_relevel (le_sup_right : LC ≤ LA ⊔ LC) fC₀
  obtain ⟨L₁, fin₁, h₁, gc₁, hgc₁, -, g₁, hg₁, -, lev₁, hlev₁, hsq₁⟩ :=
    exists_relevel_hom_comp_eq (LA ⊔ LC) hgC₁ hgA₁ E.lev rfl

  obtain ⟨X₁, f₁, C₁, lev₁, g₁, gc₁, cs₁, qs₁, lft₁, hg₁, hgc₁, hsq₁⟩ :
      ∃ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Spec (CommRingCat.of ↥L₁)) (C₁ : Scheme.{0}) (lev₁ : C₁ ⟶ X₁)
        (g₁ : E.A ⟶ X₁) (gc₁ : E.C ⟶ C₁) (_ : CompactSpace X₁) (_ : QuasiSeparatedSpace X₁) (_ : LocallyOfFiniteType f₁),
        CategoryTheory.IsPullback g₁ E.f f₁ (ιK L₁) ∧
        CategoryTheory.IsPullback gc₁ (E.lev ≫ E.f) (lev₁ ≫ f₁) (ιK L₁) ∧ E.lev ≫ g₁ = gc₁ ≫ lev₁ :=
    ⟨_, _, _, lev₁, g₁, gc₁, compactSpace_relevel h₁ _, quasiSeparatedSpace_relevel h₁ _, inferInstance, hg₁,
      by rw [hlev₁]; exact hgc₁, hsq₁⟩
  haveI := fin₁
  haveI := cs₁
  haveI := qs₁
  haveI := lft₁

  have hCsq₁ : CategoryTheory.IsPullback E.lev gc₁ g₁ lev₁ :=
    CategoryTheory.IsPullback.of_right hgc₁.flip hsq₁ hg₁.flip
  haveI : IsClosedImmersion lev₁ := by
    haveI := E.lev_closed
    haveI := isClosedImmersion_descendsAlong.{0}
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion) (Q := Fpqc) hCsq₁
      (fpqc_of_isPullback_specMap_of_field _ hg₁) ‹_›

  haveI : QuasiCompact f₁ := (quasiCompact_iff_compactSpace f₁).mpr cs₁
  haveI : QuasiSeparated f₁ := QuasiSeparated.of_quasiSeparatedSpace f₁
  obtain ⟨Lm, finm, h₁m, HW4⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_intermediateField_forall_exists_relativeGroupLaw_of_isPullback_algebraMap
      ℚ (AlgebraicClosure ℚ) L₁ E.f E.L f₁ g₁ hg₁
  obtain ⟨Lι, finι, h₁ι, HW5⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
      hΛ ℚ (AlgebraicClosure ℚ) L₁ E f₁ g₁ hg₁
  haveI := finm
  haveI := finι
  let Kf : IntermediateField ℚ (AlgebraicClosure ℚ) := Lm ⊔ Lι
  haveI : FiniteDimensional ℚ ↥Kf := IntermediateField.finiteDimensional_sup Lm Lι
  have h₁f : L₁ ≤ Kf := h₁m.trans le_sup_left

  obtain ⟨r, hr, hrq⟩ := exists_relevel h₁f hg₁
  let j : ↥L₁ →+* ↥Kf := (IntermediateField.inclusion h₁f).toRingHom
  have hj : ∀ x : ↥L₁, ((j x : ↥Kf) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun x => rfl
  have hq : CategoryTheory.IsPullback (pullback.fst f₁ (ιLL' h₁f)) (pullback.snd f₁ (ιLL' h₁f)) f₁
      (Spec.map (CommRingCat.ofHom j)) := CategoryTheory.IsPullback.of_hasPullback _ _
  obtain ⟨G₂, hmul, hcomm⟩ := HW4 Kf le_sup_left j hj _ _ r hr _ hq hrq
  obtain ⟨act₂, hact₂, hequiv, hhom, hone, hmul₂, hadd⟩ := HW5 Kf le_sup_right j hj _ _ r hr _ hq hrq G₂ hmul

  clear HW4 HW5
  obtain ⟨X₂, f₂, q, r, hr, hrq, hq, G₂, hmul, hcomm, act₂, hact₂, hequiv, hhom, hone, hmul₂, hadd⟩ :
      ∃ (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥Kf)) (q : X₂ ⟶ X₁) (r : E.A ⟶ X₂)
        (hr : CategoryTheory.IsPullback r E.f f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥Kf (AlgebraicClosure ℚ)))))
        (_ : r ≫ q = g₁) (_ : CategoryTheory.IsPullback q f₂ f₁ (Spec.map (CommRingCat.ofHom j)))
        (G₂ : RelativeGroupLaw ↥Kf f₂)
        (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ r =
            (G₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Kf (AlgebraicClosure ℚ))))
              ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1)
        (_ : E.L.IsCommutative → G₂.IsCommutative)
        (act₂ : ↥Λ → (X₂ ⟶ X₂)) (hact₂ : ∀ x : ↥Λ, act₂ x ≫ f₂ = f₂),
          (∀ x : ↥Λ, E.act x ≫ r = r ≫ act₂ x) ∧
          (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥Kf)) (P Q : SchemeHomOver t f₂),
            pushPt (act₂ x) (hact₂ x) (G₂.mul t P Q) =
              G₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ x) (hact₂ x) Q)) ∧
          (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₂ ⟨1, h⟩ = 𝟙 X₂) ∧
          (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            act₂ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₂ y ≫ act₂ x) ∧
          (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥Kf)) (P : SchemeHomOver t f₂),
            pushPt (act₂ (x + y)) (hact₂ (x + y)) P =
              G₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ y) (hact₂ y) P)) :=
    ⟨_, _, _, r, hr, hrq, hq, G₂, hmul, hcomm, act₂, hact₂, hequiv, hhom, hone, hmul₂, hadd⟩

  let lev₂ : pullback lev₁ q ⟶ X₂ := pullback.snd lev₁ q
  let gc₂ : E.C ⟶ pullback lev₁ q := pullback.lift gc₁ (E.lev ≫ r) (by rw [Category.assoc, hrq, hsq₁])
  have hgc₂_fst : gc₂ ≫ pullback.fst lev₁ q = gc₁ := pullback.lift_fst _ _ _
  have hgc₂_snd : gc₂ ≫ lev₂ = E.lev ≫ r := pullback.lift_snd _ _ _
  have hCsq₂ : CategoryTheory.IsPullback E.lev gc₂ r lev₂ := by
    refine CategoryTheory.IsPullback.of_bot ?_ hgc₂_snd.symm (CategoryTheory.IsPullback.of_hasPullback lev₁ q).flip
    rw [hgc₂_fst, hrq]
    exact hCsq₁
  have hCK : CategoryTheory.IsPullback gc₂ (E.lev ≫ E.f) (lev₂ ≫ f₂)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Kf (AlgebraicClosure ℚ)))) := hCsq₂.flip.paste_vert hr

  have hgm : IsHomAlong (algebraMap ↥Kf (AlgebraicClosure ℚ)) G₂ E.L r hr := ⟨fun t' P Q => hmul t' P Q⟩
  haveI := surjective_specMap_of_field (algebraMap ↥Kf (AlgebraicClosure ℚ))
  haveI := flat_specMap_of_field (algebraMap ↥Kf (AlgebraicClosure ℚ))
  have hfp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥Kf)),
      Fpqc (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap ↥Kf (AlgebraicClosure ℚ))))) :=
    fun t => ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : ConnectedSpace E.A := connectedSpace_of_forall_isConnected_preimage E.f E.bundle.connectedFibres
  haveI : ConnectedSpace X₂ := connectedSpace_of_isPullback _ hr
  haveI := E.bundle.smooth
  haveI := E.bundle.proper
  haveI := CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two (AlgebraicClosure ℚ) E
  haveI : SmoothOfRelativeDimension 2 f₂ := smoothOfRelativeDimension_of_isPullback _ hr 2
  haveI := E.lev_finitePresentation
  haveI : IsFinite (lev₂ ≫ f₂) := isFinite_of_isPullback _ hCK
  haveI : Flat (lev₂ ≫ f₂) := inferInstance
  refine ⟨Kf, inferInstance,
    { A := X₂
      f := f₂
      L := G₂
      comm := hcomm E.comm
      bundle := ⟨smooth_of_isPullback _ hr, isProper_of_isPullback _ hr,
        fun s => isConnected_preimage_of_connectedSpace f₂ s, ⟨G₂⟩⟩
      dim_fibre := fun s => by
        rw [topologicalKrullDim_preimage_eq, topologicalKrullDim_eq_of_smoothOfRelativeDimension f₂ 2]
        rfl
      act := act₂
      act_over := hact₂
      act_hom := hhom
      act_one := hone
      act_mul := hmul₂
      act_add := hadd
      act_trace := fun k _ _ sk V _ _ _ τ hτi hτr hτa hτs m Φ hΦ n hn => by
        obtain ⟨σ, rfl⟩ := exists_ringHom_comp_algebraMap_eq Kf sk
        obtain ⟨τ', h1, h2, h3, h4, h5⟩ :=
          trace_transfer hgm k σ V τ hτi hτr hτa hτs (E.act_over m) (hact₂ m) (hequiv m) Φ hΦ
        exact E.act_trace k σ V τ' h1 h2 h3 h4 m Φ h5 n hn
      C := pullback lev₁ q
      lev := lev₂
      lev_closed := inferInstance
      lev_sub := @fun T t P Q hP hQ => by
        rw [factorsThrough_iff_factorsThrough_liftPt (hg := hr) hCsq₂ hfp] at hP hQ
        rw [factorsThrough_iff_factorsThrough_liftPt (hg := hr) hCsq₂ hfp,
          factorsThrough_iff_factorsThrough_liftPt (hg := hr) hCsq₂ hfp, liftPt_mul hgm, liftPt_inv hgm]
        exact E.lev_sub _ _ _ hP hQ
      lev_one := @fun T t => by
        rw [factorsThrough_iff_factorsThrough_liftPt (hg := hr) hCsq₂ hfp, liftPt_one hgm]
        exact E.lev_one _
      lev_torsion := @fun T t P hP => by
        apply liftPt_injective (hg := hr) hfp
        rw [liftPt_nsmul hgm, liftPt_one hgm]
        exact E.lev_torsion _ _ ((factorsThrough_iff_factorsThrough_liftPt (hg := hr) hCsq₂ hfp _).mp hP)
      lev_stable := @fun x T t P hP => by
        rw [factorsThrough_iff_factorsThrough_liftPt (hg := hr) hCsq₂ hfp] at hP ⊢
        rw [liftPt_pushPt (E.act_over x) (hact₂ x) (hequiv x)]
        exact E.lev_stable x _ _ hP
      lev_finite := inferInstance
      lev_flat := inferInstance
      lev_finitePresentation := locallyOfFinitePresentation_of_isPullback _ hCK
      lev_rank := fun s => by
        have h := Scheme.Hom.finrank_of_isPullback gc₂ (E.lev ≫ E.f) (lev₂ ≫ f₂) _ hCK default
        rw [E.lev_rank] at h
        rw [Subsingleton.elim s ((Spec.map (CommRingCat.ofHom (algebraMap ↥Kf (AlgebraicClosure ℚ)))).base default)]
        exact h.symm
      lev_fibre := fun k _ _ sk hN => by
        obtain ⟨σ, rfl⟩ := exists_ringHom_comp_algebraMap_eq Kf sk
        obtain ⟨e, he⟩ := E.lev_fibre k σ hN
        exact levFibre_transfer hgm hCsq₂ k σ e he }, r, hr, hmul, hequiv, ?_⟩

  rintro T t' P ⟨P₀, hP₀⟩
  exact ⟨P₀ ≫ gc₂, by rw [Category.assoc, hgc₂_snd, ← Category.assoc, hP₀]⟩

end Main

end CerednikDrinfeld.QM.FakeEllipticCurve.NFDescent
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM.FakeEllipticCurve.NFDescent"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM.FakeEllipticCurve"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM.FakeEllipticCurve P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM.FakeEllipticCurve.NFDescent"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld _root_.CerednikDrinfeld.QM _root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg.CerednikDrinfeld.QM in
open scoped Quaternion in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : Λ.FG) (N : ℕ)
    (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (E₀ : FakeEllipticCurve Λ N K),
      FakeEllipticCurve.IsPullback (algebraMap K (AlgebraicClosure ℚ)) E₀ E :=
  CerednikDrinfeld.QM.FakeEllipticCurve.NFDescent.exists_numberField_model Λ hΛ N E

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_isPullback_algebraMap_of_fg (solution)
