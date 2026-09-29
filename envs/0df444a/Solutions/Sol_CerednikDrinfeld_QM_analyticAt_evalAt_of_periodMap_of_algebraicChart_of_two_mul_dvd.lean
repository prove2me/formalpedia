-- Prove2me | solution 1 for CerednikDrinfeld.QM.analyticAt_evalAt_of_periodMap_of_algebraicChart_of_two_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/beebdb86-1950-5cae-ae88-2ad7042c690a

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_analyticAt_evalAt_of_periodMap_of_algebraicChart_of_two_mul_dvd
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

namespace ChartHolP6b

theorem germ_stalkClosedPointTo_SpecMap_comp {C : Scheme.{0}} {R : CommRingCat.{0}}
    (χ : R ⟶ CommRingCat.of ℂ) (Ψ : Spec R ⟶ C) (U : C.Opens) (hΨ : (⊤ : (Spec R).Opens) ≤ Ψ ⁻¹ᵁ U)
    (hmem : (Spec.map χ ≫ Ψ).base (IsLocalRing.closedPoint ℂ) ∈ U) :
    C.presheaf.germ U _ hmem ≫ Scheme.stalkClosedPointTo (Spec.map χ ≫ Ψ) =
      Ψ.app U ≫ (Spec R).presheaf.map (homOfLE hΨ).op ≫ (Scheme.ΓSpecIso R).hom ≫ χ := by
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc Ψ U ((Spec.map χ).base (IsLocalRing.closedPoint ℂ)) hmem]
  rw [← TopCat.Presheaf.germ_res (Spec R).presheaf (homOfLE hΨ) _ trivial, Category.assoc,
    Scheme.germ_stalkClosedPointTo_Spec]

theorem stalkClosedPointTo_SpecMap_comp_germ {C : Scheme.{0}} {R : CommRingCat.{0}}
    (χ : R ⟶ CommRingCat.of ℂ) (Ψ : Spec R ⟶ C) (U : C.Opens) (hΨ : (⊤ : (Spec R).Opens) ≤ Ψ ⁻¹ᵁ U) (t : Γ(C, U))
    (hmem : (Spec.map χ ≫ Ψ).base (IsLocalRing.closedPoint ℂ) ∈ U) :
    (Scheme.stalkClosedPointTo (Spec.map χ ≫ Ψ)).hom ((C.presheaf.germ U _ hmem).hom t) =
      χ.hom ((Scheme.ΓSpecIso R).hom.hom (((Spec R).presheaf.map (homOfLE hΨ).op).hom ((Ψ.app U).hom t))) := by
  have := congrArg (fun φ => φ.hom t) (germ_stalkClosedPointTo_SpecMap_comp χ Ψ U hΨ hmem)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this

theorem algebraMap_germ_eq {C : Scheme.{0}} [IsIntegral C] (U : C.Opens) (x : C) (hx : x ∈ U) (t : Γ(C, U)) :
    algebraMap (C.presheaf.stalk x) C.functionField ((C.presheaf.germ U x hx).hom t) =
      (C.presheaf.germ U (genericPoint C) (((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩)).hom t := by
  change (C.presheaf.germ U x hx ≫ C.presheaf.stalkSpecializes _).hom t = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem core
    {B : Type} [CommRing B] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of B))
    (sC : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of B))
    {Fc : Type} [Field Fc] [Algebra ℂ Fc] (𝔐c : AlgebraicCurve.CurveModel ℂ Fc)
    (e𝔐c : 𝔐c.C ⟶ pullback πX sC) [IsIso e𝔐c] (he𝔐c_snd : e𝔐c ≫ pullback.snd πX sC = 𝔐c.toBase)
    (FE : ∀ (S : Type) [CommRing S], Type 1)
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FE S → SchemeHomOver s πX)
    (IsoC : FE ℂ → FE ℂ → Prop)
    (pt_iso : ∀ (s : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of B)) (E E' : FE ℂ), IsoC E E' → pt ℂ s E = pt ℂ s E')
    (IsPB : ∀ (S S' : Type) [CommRing S] [CommRing S'], (S →+* S') → FE S → FE S' → Prop)
    (exists_pb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (E : FE S), ∃ E' : FE S', IsPB S S' φ E E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FE S) (E' : FE S'), IsPB S S' φ E E' →
        (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    {O : Type} (orb : UpperHalfPlane → O) (perE : FE ℂ → UpperHalfPlane)
    (hper1 : ∀ E E' : FE ℂ, IsoC E E' ↔ orb (perE E) = orb (perE E'))
    (hchart : ∀ τ₀ : UpperHalfPlane,
      ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S) (_ : Algebra.FiniteType ℂ S)
        (𝒜 : FE S) (W : Set UpperHalfPlane) (h : UpperHalfPlane → (S →ₐ[ℂ] ℂ)),
        IsOpen W ∧ τ₀ ∈ W ∧ Set.InjOn h W ∧
        (∀ s : S, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W} ∧
          ∀ z : ℂ, 0 < z.im → UpperHalfPlane.ofComplex z ∈ W → F z = h (UpperHalfPlane.ofComplex z) s) ∧
        (∀ τ ∈ W, ∀ E' : FE ℂ, IsPB S ℂ (h τ).toRingHom 𝒜 E' → orb (perE E') = orb τ)) :
    ∀ (τ₀ : UpperHalfPlane) (E₀ : FE ℂ) (𝔓₀ : Place ℂ Fc),
      (pt _ sC E₀).1 = (𝔐c.pointEquivPlace.symm 𝔓₀).1 ≫ e𝔐c ≫ pullback.fst πX sC →
      orb τ₀ = orb (perE E₀) →
      ∀ x : Fc, x ∈ 𝔓₀.toValuationSubring →
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧
          ∀ᶠ τ in 𝓝 τ₀, ∀ (E : FE ℂ) (𝔓 : Place ℂ Fc),
            (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ pullback.fst πX sC →
            orb τ = orb (perE E) → x ∈ 𝔓.toValuationSubring ∧ F (τ : ℂ) = 𝔓.evalAt x := by
  intro τ₀ E₀ 𝔓₀ hlink₀ horb₀ x hx
  classical

  obtain ⟨S, _i1, _i2, _i3, _i4, 𝒜, W, h, hWo, hτ₀W, -, hchar, hfib⟩ := hchart τ₀

  set sS : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) ≫ sC
    with hsS
  have hφ_over : (pt S sS 𝒜).1 ≫ πX = Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) ≫ sC := (pt S sS 𝒜).2
  set Θ : Spec (CommRingCat.of S) ⟶ 𝔐c.C :=
    pullback.lift (pt S sS 𝒜).1 (Spec.map (CommRingCat.ofHom (algebraMap ℂ S))) hφ_over ≫ inv e𝔐c with hΘ
  have hΘe : Θ ≫ e𝔐c = pullback.lift (pt S sS 𝒜).1 (Spec.map (CommRingCat.ofHom (algebraMap ℂ S))) hφ_over := by
    rw [hΘ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hΘ_fst : Θ ≫ e𝔐c ≫ pullback.fst πX sC = (pt S sS 𝒜).1 := by
    rw [← Category.assoc, hΘe, pullback.lift_fst]
  have hΘ_snd : Θ ≫ e𝔐c ≫ pullback.snd πX sC = Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
    rw [← Category.assoc, hΘe, pullback.lift_snd]
  have hΘ_base : Θ ≫ 𝔐c.toBase = Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
    rw [← he𝔐c_snd, hΘ_snd]
  have hχid : ∀ χ : S →ₐ[ℂ] ℂ,
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) = 𝟙 _ := by
    intro χ
    rw [AlgHom.toRingHom_eq_coe, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap, Algebra.algebraMap_self,
      CommRingCat.ofHom_id, Spec.map_id]
  have point_over : ∀ χ : S →ₐ[ℂ] ℂ, (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Θ) ≫ 𝔐c.toBase = 𝟙 _ := fun χ => by
    rw [Category.assoc, hΘ_base, hχid]
  let P : (S →ₐ[ℂ] ℂ) → {p : Spec (CommRingCat.of ℂ) ⟶ 𝔐c.C // p ≫ 𝔐c.toBase = 𝟙 _} := fun χ => ⟨_, point_over χ⟩
  have hP1 : ∀ χ : S →ₐ[ℂ] ℂ, (P χ).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Θ := fun χ => rfl

  have place_eq : ∀ τ ∈ W, ∀ (E : FE ℂ) (𝔓 : Place ℂ Fc),
      (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ pullback.fst πX sC → orb τ = orb (perE E) →
      𝔓 = 𝔐c.pointEquivPlace (P (h τ)) := by
    intro τ hτ E 𝔓 hlink horb
    obtain ⟨E', hE'⟩ := exists_pb S ℂ (h τ).toRingHom 𝒜
    have hcomm : Spec.map (CommRingCat.ofHom (h τ).toRingHom) ≫ sS = sC := by
      rw [hsS, ← Category.assoc, hχid, Category.id_comp]
    have hpt' : (pt ℂ sC E').1 = Spec.map (CommRingCat.ofHom (h τ).toRingHom) ≫ (pt S sS 𝒜).1 :=
      pt_pullback S ℂ (h τ).toRingHom sS sC hcomm 𝒜 E' hE'
    have horb' : orb (perE E') = orb τ := hfib τ hτ E' hE'
    have hiso : IsoC E E' := (hper1 E E').2 (by rw [← horb, horb'])
    have hptE : (pt ℂ sC E).1 = Spec.map (CommRingCat.ofHom (h τ).toRingHom) ≫ (pt S sS 𝒜).1 := by
      rw [pt_iso sC E E' hiso, hpt']
    apply CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq 𝔐c πX sC e𝔐c inferInstance he𝔐c_snd
    rw [Equiv.symm_apply_apply, hP1, ← hlink, hptE, Category.assoc, hΘ_fst]

  have h𝔓₀ : 𝔓₀ = 𝔐c.pointEquivPlace (P (h τ₀)) := place_eq τ₀ hτ₀W E₀ 𝔓₀ hlink₀ horb₀
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : 𝔐c.C.presheaf.stalk ((P (h τ₀)).1.base (IsLocalRing.closedPoint ℂ)),
      𝔐c.ffEquiv.symm (algebraMap _ 𝔐c.C.functionField s₀) = x := by
    have hx' : x ∈ (𝔐c.placeOfPoint (pointEquivClosedPoint 𝔐c.toBase (P (h τ₀)))).toValuationSubring.toSubring := by
      rw [← CurveModel.pointEquivPlace_apply, ← h𝔓₀]; exact hx
    rw [← 𝔐c.range_stalk_eq (pointEquivClosedPoint 𝔐c.toBase (P (h τ₀)))] at hx'
    obtain ⟨s₀, hs₀⟩ := RingHom.mem_range.1 hx'
    exact ⟨s₀, hs₀⟩
  obtain ⟨U, hP₀U, t, ht⟩ : ∃ (U : 𝔐c.C.Opens) (m : (P (h τ₀)).1.base (IsLocalRing.closedPoint ℂ) ∈ U) (t : Γ(𝔐c.C, U)),
      (𝔐c.C.presheaf.germ U _ m).hom t = s₀ := TopCat.Presheaf.exists_germ_eq 𝔐c.C.presheaf s₀

  have h𝔭₀ : (Spec.map (CommRingCat.ofHom (h τ₀).toRingHom)).base (IsLocalRing.closedPoint ℂ) ∈ (Θ ⁻¹ᵁ U : Set _) := hP₀U
  obtain ⟨_, ⟨g, rfl⟩, hg𝔭₀, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭₀ (Θ ⁻¹ᵁ U).isOpen
  have hg0 : (h τ₀) g ≠ 0 := by
    intro h0
    apply (PrimeSpectrum.mem_basicOpen _ _).1 hg𝔭₀
    change (h τ₀).toRingHom g ∈ IsLocalRing.maximalIdeal ℂ
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0]
    exact not_isUnit_zero

  set ιg : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) with hιg
  have hrange : Set.range (ιg ≫ Θ) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hy : ιg.base y ∈ ((PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum S)) :
        Set (PrimeSpectrum S)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨y, rfl⟩
    exact hgU hy
  set ΘU : Spec (CommRingCat.of (Localization.Away g)) ⟶ (U : Scheme.{0}) := IsOpenImmersion.lift U.ι (ιg ≫ Θ) hrange
    with hΘU
  have hΘUι : ΘU ≫ U.ι = ιg ≫ Θ := IsOpenImmersion.lift_fac _ _ _
  have hΨU : (⊤ : (Spec (CommRingCat.of (Localization.Away g))).Opens) ≤ (ΘU ≫ U.ι) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

  set c : Localization.Away g := (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away g))).hom.hom
    (((Spec (CommRingCat.of (Localization.Away g))).presheaf.map (homOfLE hΨU).op).hom (((ΘU ≫ U.ι).app U).hom t))
    with hc
  obtain ⟨n, bb, hcb⟩ := IsLocalization.Away.surj g c

  obtain ⟨Fb, hFb_diff, hFb⟩ := hchar bb
  obtain ⟨Fg, hFg_diff, hFg⟩ := hchar g
  have hD : {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W} ∈ 𝓝 (τ₀ : ℂ) := by
    have h1 : ((↑) : UpperHalfPlane → ℂ) '' W ∈ 𝓝 (τ₀ : ℂ) :=
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap W hWo).mem_nhds ⟨τ₀, hτ₀W, rfl⟩
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨τ, hτ, rfl⟩
    exact ⟨τ.im_pos, by rw [UpperHalfPlane.ofComplex_apply]; exact hτ⟩
  have hFgτ₀ : Fg (τ₀ : ℂ) = (h τ₀) g := by
    rw [hFg _ τ₀.im_pos (by rw [UpperHalfPlane.ofComplex_apply]; exact hτ₀W), UpperHalfPlane.ofComplex_apply]
  have hne : Fg (τ₀ : ℂ) ≠ 0 := by rw [hFgτ₀]; exact hg0
  refine ⟨fun z => Fb z / Fg z ^ n, (hFb_diff.analyticAt hD).div ((hFg_diff.analyticAt hD).pow n) (pow_ne_zero n hne), ?_⟩

  have hev1 : ∀ᶠ τ : UpperHalfPlane in 𝓝 τ₀, τ ∈ W := hWo.mem_nhds hτ₀W
  have hev2 : ∀ᶠ τ : UpperHalfPlane in 𝓝 τ₀, Fg (τ : ℂ) ≠ 0 :=
    UpperHalfPlane.continuous_coe.continuousAt.eventually ((hFg_diff.analyticAt hD).continuousAt.eventually_ne hne)
  filter_upwards [hev1, hev2] with τ hτW hτg
  intro E 𝔓 hlink horb
  have hτg' : (h τ) g ≠ 0 := by
    rwa [hFg _ τ.im_pos (by rw [UpperHalfPlane.ofComplex_apply]; exact hτW), UpperHalfPlane.ofComplex_apply] at hτg
  have hunit : IsUnit ((h τ).toRingHom g) := isUnit_iff_ne_zero.2 hτg'
  set χ' : Localization.Away g →+* ℂ := IsLocalization.Away.lift g hunit with hχ'
  have hχ'comp : χ'.comp (algebraMap S (Localization.Away g)) = (h τ).toRingHom := IsLocalization.Away.lift_comp g hunit
  have hPfac : Spec.map (CommRingCat.ofHom (h τ).toRingHom) ≫ Θ = Spec.map (CommRingCat.ofHom χ') ≫ (ΘU ≫ U.ι) := by
    rw [hΘUι, hιg, ← hχ'comp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hQover : (Spec.map (CommRingCat.ofHom χ') ≫ (ΘU ≫ U.ι)) ≫ 𝔐c.toBase = 𝟙 _ := by
    rw [← hPfac]; exact point_over (h τ)
  have h𝔓 : 𝔓 = 𝔐c.pointEquivPlace ⟨Spec.map (CommRingCat.ofHom χ') ≫ (ΘU ≫ U.ι), hQover⟩ := by
    rw [place_eq τ hτW E 𝔓 hlink horb]
    congr 1
    exact Subtype.ext hPfac
  subst h𝔓

  have hmemU : (Spec.map (CommRingCat.ofHom χ') ≫ (ΘU ≫ U.ι)).base (IsLocalRing.closedPoint ℂ) ∈ U :=
    (ΘU.base ((Spec.map (CommRingCat.ofHom χ')).base (IsLocalRing.closedPoint ℂ))).2
  have hxτ : 𝔐c.ffEquiv.symm (algebraMap _ 𝔐c.C.functionField ((𝔐c.C.presheaf.germ U _ hmemU).hom t)) = x := by
    rw [algebraMap_germ_eq, ← hs₀, ← ht, algebraMap_germ_eq]
  obtain ⟨hmem𝒪, -, heval⟩ := CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo 𝔐c
    ⟨Spec.map (CommRingCat.ofHom χ') ≫ (ΘU ≫ U.ι), hQover⟩ ((𝔐c.C.presheaf.germ U _ hmemU).hom t)
  rw [hxτ] at hmem𝒪 heval
  refine ⟨hmem𝒪, ?_⟩
  rw [heval]
  show Fb (τ : ℂ) / Fg (τ : ℂ) ^ n = _
  rw [stalkClosedPointTo_SpecMap_comp_germ (CommRingCat.ofHom χ') (ΘU ≫ U.ι) U hΨU t hmemU, CommRingCat.hom_ofHom, ← hc,
    hFb _ τ.im_pos (by rw [UpperHalfPlane.ofComplex_apply]; exact hτW),
    hFg _ τ.im_pos (by rw [UpperHalfPlane.ofComplex_apply]; exact hτW), UpperHalfPlane.ofComplex_apply]
  have e1 : ∀ a : S, χ' (algebraMap S (Localization.Away g) a) = (h τ) a := fun a => by
    rw [hχ', IsLocalization.Away.lift_eq]; rfl
  have key := congrArg χ' hcb
  rw [map_mul, map_pow, e1, e1] at key
  rw [div_eq_iff (pow_ne_zero n hτg')]
  exact key.symm

end ChartHolP6b

open ChartHolP6b in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))

    (Fc₀ : Type) [Field Fc₀] [Algebra ℂ Fc₀] [AlgebraicCurve.IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (U₀ : ModularCurve.UniformizedHeckeCurve (fuchsianGroup R ι) Fc₀)
    (h₀ :
      Function.Surjective U₀.pt ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
        (U₀.heckePoints ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (x : Fc₀) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => U₀.realize x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x + y) z = U₀.realize x z + U₀.realize y z) ∧
      (∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x * y) z = U₀.realize x z * U₀.realize y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (algebraMap ℂ Fc₀ c) z = c) ∧
      (∀ x y : Fc₀, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = U₀.realize y z) → x = y) ∧
      (∀ x : Fc₀, ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x (γ • z) = U₀.realize x z) ∧
      (∀ f : UpperHalfPlane → ℂ, (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
        (∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
        ∃ x : Fc₀, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = f z))

    (sC : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (𝔐c : AlgebraicCurve.CurveModel ℂ Fc)
    (e𝔐c : 𝔐c.C ⟶ CategoryTheory.Limits.pullback πX sC) (he𝔐c : IsIso e𝔐c)
    (he𝔐c_snd : e𝔐c ≫ CategoryTheory.Limits.pullback.snd πX sC = 𝔐c.toBase)

    (perE : FakeEllipticCurve Λ N ℂ → UpperHalfPlane)
    (hper :

      (∀ E E' : FakeEllipticCurve Λ N ℂ,
        FakeEllipticCurve.Iso E E' ↔ U₀.pt (perE E) = U₀.pt (perE E')) ∧

      (∀ τ : UpperHalfPlane, ∃ E : FakeEllipticCurve Λ N ℂ, U₀.pt (perE E) = U₀.pt τ))

    (hchart : ∀ τ₀ : UpperHalfPlane,
      ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S) (_ : Algebra.FiniteType ℂ S)
        (𝒜 : FakeEllipticCurve Λ N S) (W : Set UpperHalfPlane) (h : UpperHalfPlane → (S →ₐ[ℂ] ℂ)),
        IsOpen W ∧ τ₀ ∈ W ∧ Set.InjOn h W ∧
        (∀ s : S, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W} ∧
          ∀ z : ℂ, 0 < z.im → UpperHalfPlane.ofComplex z ∈ W → F z = h (UpperHalfPlane.ofComplex z) s) ∧
        (∀ τ ∈ W, ∀ E' : FakeEllipticCurve Λ N ℂ,
          FakeEllipticCurve.IsPullback (h τ).toRingHom 𝒜 E' → U₀.pt (perE E') = U₀.pt τ)) :

    ∀ (τ₀ : UpperHalfPlane) (E₀ : FakeEllipticCurve Λ N ℂ) (𝔓₀ : Place ℂ Fc),
      (pt _ sC E₀).1 = (𝔐c.pointEquivPlace.symm 𝔓₀).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
      U₀.pt τ₀ = U₀.pt (perE E₀) →
      ∀ x : Fc, x ∈ 𝔓₀.toValuationSubring →
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧
          ∀ᶠ τ in 𝓝 τ₀, ∀ (E : FakeEllipticCurve Λ N ℂ) (𝔓 : Place ℂ Fc),
            (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
            U₀.pt τ = U₀.pt (perE E) → x ∈ 𝔓.toValuationSubring ∧ F (τ : ℂ) = 𝔓.evalAt x := by
  haveI := he𝔐c
  exact ChartHolP6b.core πX sC 𝔐c e𝔐c he𝔐c_snd (fun S _ => FakeEllipticCurve Λ N S) pt
    (fun E E' => FakeEllipticCurve.Iso E E') (fun s E E' hI => pt_iso ℂ s E E' hI)
    (fun S S' _ _ φ E E' => FakeEllipticCurve.IsPullback φ E E')
    (fun S S' _ _ φ E => by
      obtain ⟨E', g, hg, h1, h2, h3, -⟩ := FakeEllipticCurve.exists_isPullback_levelIff φ E
      exact ⟨E', g, hg, h1, h2, h3⟩)
    (fun S S' _ _ φ s s' hs E E' hI => pt_pullback S S' φ s s' hs E E' hI)
    U₀.pt perE hper.1 hchart

end S_CerednikDrinfeld_QM_analyticAt_evalAt_of_periodMap_of_algebraicChart_of_two_mul_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_QM_analyticAt_evalAt_of_periodMap_of_algebraicChart_of_two_mul_dvd (solution)
