-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isPullbackVia_isFormalModuleVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7c0cc266-0bb3-5278-a565-9243419fa29d

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_isFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField

namespace FCCBody

open TopologicalSpace

section Topology

variable {R : Type} [CommRing R]

theorem isOpen_connectedComponent_prime [IsNoetherianRing R] (x : PrimeSpectrum R) :
    IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents (PrimeSpectrum R)).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum R) | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion₂, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩, mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hz hzx
      apply hy
      have h1 : irreducibleComponent y ⊆ connectedComponent z :=
        isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent hz
      rw [connectedComponent_eq hzx]
      exact h1 mem_irreducibleComponent
    · rintro ⟨Z, ⟨-, hZ⟩, hyZ⟩ hyx
      exact Set.disjoint_left.1 hZ hyZ hyx
  have hclosed : IsClosed (connectedComponent x)ᶜ := by
    rw [hcompl]
    refine Set.Finite.isClosed_biUnion (hfin.subset (fun Z hZ => hZ.1)) ?_
    intro Z hZ
    exact isClosed_of_mem_irreducibleComponents Z hZ.1
  exact isClosed_compl_iff.1 hclosed

theorem exists_finset_span_eq_top_isConnected_basicOpen [IsNoetherianRing R] :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ e ∈ t, _root_.IsConnected (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
  classical
  have hclopen : ∀ x : PrimeSpectrum R, IsClopen (connectedComponent x) := fun x =>
    ⟨isClosed_connectedComponent, isOpen_connectedComponent_prime x⟩
  choose ε hε using fun x : PrimeSpectrum R => PrimeSpectrum.isClopen_iff.1 (hclopen x)
  have hfin : (irreducibleComponents (PrimeSpectrum R)).Finite := NoetherianSpace.finite_irreducibleComponents
  have hne : ∀ Z ∈ irreducibleComponents (PrimeSpectrum R), Z.Nonempty := fun Z hZ => hZ.1.nonempty
  choose pt hpt using hne
  refine ⟨hfin.toFinset.attach.image (fun Z => ε (pt Z.1 (hfin.mem_toFinset.1 Z.2))), ?_, ?_⟩
  · by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    let 𝔭 : PrimeSpectrum R := ⟨M, hM.isPrime⟩
    have hZ : irreducibleComponent 𝔭 ∈ irreducibleComponents (PrimeSpectrum R) :=
      irreducibleComponent_mem_irreducibleComponents 𝔭
    have hZf : irreducibleComponent 𝔭 ∈ hfin.toFinset := hfin.mem_toFinset.2 hZ
    have hsub : irreducibleComponent 𝔭 ⊆ connectedComponent (pt _ hZ) :=
      isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent (hpt _ hZ)
    have h𝔭 : 𝔭 ∈ connectedComponent (pt _ hZ) := hsub mem_irreducibleComponent
    rw [(hε _).2] at h𝔭
    have h2 : ε (pt _ hZ) ∉ M := (PrimeSpectrum.mem_basicOpen _ _).1 h𝔭
    apply h2
    apply hle
    apply Ideal.subset_span
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨_, hZf⟩, Finset.mem_attach _ _, rfl⟩)
  · intro e he
    obtain ⟨Z, -, rfl⟩ := Finset.mem_image.1 he
    rw [← (hε _).2]
    exact isConnected_connectedComponent

theorem eq_zero_or_one_of_preconnectedSpace {S : Type} [CommRing S] [PreconnectedSpace (PrimeSpectrum S)]
    (e : S) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hclo : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum S)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩
  have key : ∀ f : S, IsIdempotentElem f → (∀ 𝔭 : PrimeSpectrum S, f ∈ 𝔭.asIdeal) → f = 0 := by
    intro f hf hall
    have hnil : IsNilpotent f := nilpotent_iff_mem_prime.2 (fun J hJ => hall ⟨J, hJ⟩)
    obtain ⟨n, hn⟩ := hnil
    cases n with
    | zero =>
      have h10 : (1 : S) = 0 := by simpa using hn
      calc f = f * 1 := (mul_one f).symm
        _ = 0 := by rw [h10, mul_zero]
    | succ n => rw [← hf.pow_succ_eq n, hn]
  rcases isClopen_iff.1 hclo with h | h
  · left
    apply key e he
    intro 𝔭
    by_contra hh
    have hmem : 𝔭 ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum S)) := (PrimeSpectrum.mem_basicOpen _ _).2 hh
    rw [h] at hmem
    exact hmem
  · right
    have h1e : 1 - e = 0 := by
      apply key (1 - e) he.one_sub
      intro 𝔭
      have hmem : 𝔭 ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum S)) := by rw [h]; trivial
      have he𝔭 : e ∉ 𝔭.asIdeal := (PrimeSpectrum.mem_basicOpen _ _).1 hmem
      have hprod : e * (1 - e) ∈ 𝔭.asIdeal := by
        rw [mul_sub, mul_one, he.eq, sub_self]; exact Ideal.zero_mem _
      exact (𝔭.isPrime.mem_or_mem hprod).resolve_left he𝔭
    have := sub_eq_zero.1 h1e
    exact this.symm

theorem preconnectedSpace_of_isConnected_basicOpen {S : Type} [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (h : _root_.IsConnected (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))) :
    PreconnectedSpace (PrimeSpectrum S) := by
  constructor
  have hind := (PrimeSpectrum.localization_away_isOpenEmbedding S r).isEmbedding.isInducing
  rw [← hind.isPreconnected_image, Set.image_univ, PrimeSpectrum.localization_away_comap_range S r]
  exact h.isPreconnected

theorem isConnected_basicOpen_mul (c b : R)
    (h : _root_.IsConnected (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away c) b) :
      Set (PrimeSpectrum (Localization.Away c)))) :
    _root_.IsConnected (PrimeSpectrum.basicOpen (c * b) : Set (PrimeSpectrum R)) := by
  have hcont : Continuous (PrimeSpectrum.comap (algebraMap R (Localization.Away c))) :=
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away c) c).continuous
  have hpre : PrimeSpectrum.comap (algebraMap R (Localization.Away c)) ⁻¹' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away c) b) : Set (PrimeSpectrum (Localization.Away c))) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    rfl
  have himg : PrimeSpectrum.comap (algebraMap R (Localization.Away c)) ''
        (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away c) b) : Set (PrimeSpectrum (Localization.Away c))) =
      (PrimeSpectrum.basicOpen (c * b) : Set (PrimeSpectrum R)) := by
    rw [← hpre, Set.image_preimage_eq_range_inter, PrimeSpectrum.localization_away_comap_range (Localization.Away c) c,
      PrimeSpectrum.basicOpen_mul, Opens.coe_inf]
  rw [← himg]
  exact h.image _ hcont.continuousOn

end Topology

section Refine

variable {B : Type} [CommRing B] [IsNoetherianRing B]

theorem exists_refine (c : B) :
    ∃ t : Finset B,
      (∀ b ∈ t, ∀ e : Localization.Away (c * b), IsIdempotentElem e → e = 0 ∨ e = 1) ∧
      ∀ 𝔭 : PrimeSpectrum B, c ∉ 𝔭.asIdeal → ∃ b ∈ t, c * b ∉ 𝔭.asIdeal := by
  classical
  obtain ⟨t₀, ht₀, hconn⟩ := exists_finset_span_eq_top_isConnected_basicOpen (R := Localization.Away c)

  have hsurj := fun z : Localization.Away c => IsLocalization.surj (Submonoid.powers c) z
  choose num hnum using hsurj

  have hbo : ∀ z : Localization.Away c,
      (PrimeSpectrum.basicOpen (algebraMap B (Localization.Away c) (num z).1) : Set (PrimeSpectrum (Localization.Away c))) =
        (PrimeSpectrum.basicOpen z : Set _) := by
    intro z
    have hu : IsUnit (algebraMap B (Localization.Away c) ((num z).2 : B)) :=
      IsLocalization.map_units (Localization.Away c) (num z).2
    ext x
    rw [← hnum z]
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    constructor
    · intro h hz
      exact h (Ideal.mul_mem_right _ _ hz)
    · intro h hzu
      exact (x.isPrime.mem_or_mem hzu).elim h (fun hu' => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu' hu))
  refine ⟨t₀.image (fun z => (num z).1), ?_, ?_⟩
  · intro b hb e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hb
    have hc : _root_.IsConnected (PrimeSpectrum.basicOpen (c * (num z).1) : Set (PrimeSpectrum B)) := by
      apply isConnected_basicOpen_mul
      rw [hbo z]
      exact hconn z hz
    haveI := preconnectedSpace_of_isConnected_basicOpen (S := Localization.Away (c * (num z).1)) (c * (num z).1) hc
    exact eq_zero_or_one_of_preconnectedSpace e he
  · intro 𝔭 h𝔭

    have hrange : 𝔭 ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away c))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away c) c]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 h𝔭
    obtain ⟨𝔮, rfl⟩ := hrange

    have hex : ∃ z ∈ t₀, z ∉ 𝔮.asIdeal := by
      by_contra hall
      have hle : Ideal.span (t₀ : Set (Localization.Away c)) ≤ 𝔮.asIdeal :=
        Ideal.span_le.2 (fun z hz => by_contra (fun hz' => hall ⟨z, hz, hz'⟩))
      rw [ht₀] at hle
      exact 𝔮.isPrime.ne_top (top_le_iff.1 hle)
    obtain ⟨z, hz, hzq⟩ := hex
    refine ⟨(num z).1, Finset.mem_image.2 ⟨z, hz, rfl⟩, ?_⟩
    have h1 : 𝔮 ∈ (PrimeSpectrum.basicOpen (algebraMap B (Localization.Away c) (num z).1) : Set _) := by
      rw [hbo z]; exact (PrimeSpectrum.mem_basicOpen _ _).2 hzq
    have h2 : (num z).1 ∉ (PrimeSpectrum.comap (algebraMap B (Localization.Away c)) 𝔮).asIdeal :=
      (PrimeSpectrum.mem_basicOpen _ _).1 h1
    exact fun hmul => ((PrimeSpectrum.comap (algebraMap B (Localization.Away c)) 𝔮).isPrime.mem_or_mem hmul).elim h𝔭 h2

end Refine

end FCCBody

namespace FCCBody

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

end FCCBody

open FCCBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] [IsNoetherianRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B) :
    ∃ s : Finset B, Ideal.span (s : Set B) = ⊤ ∧
      ∀ c ∈ s,
        (∀ e : Localization.Away c, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (∀ (E' : FakeEllipticCurve Λ N (Localization.Away c)) (g : E'.A ⟶ E.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B (Localization.Away c)) E E' g →
            ∃ (X : FormalODModule q (Localization.Away c)) (θ : RelativeGroupLaw.FormalCoordinates E'.f 2),
              E'.IsFormalModuleVia coord X θ) := by
  classical
  obtain ⟨s₀, hs₀, H⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_isFormalModuleOf coord hcoord B hq E
  choose t ht₁ ht₂ using fun c : B => FCCBody.exists_refine c
  refine ⟨s₀.biUnion (fun c => (t c).image (fun b' => c * b')), ?_, ?_⟩
  · by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hex : ∃ c ∈ s₀, c ∉ M := by
      by_contra hall
      have h1 : Ideal.span (s₀ : Set B) ≤ M :=
        Ideal.span_le.2 (fun c hc => by_contra (fun hc' => hall ⟨c, hc, hc'⟩))
      rw [hs₀] at h1
      exact hM.ne_top (top_le_iff.1 h1)
    obtain ⟨c, hc, hcM⟩ := hex
    obtain ⟨b', hb', hcb⟩ := ht₂ c ⟨M, hM.isPrime⟩ hcM
    apply hcb
    apply hle
    apply Ideal.subset_span
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_image.2 ⟨b', hb', rfl⟩⟩)
  · intro c' hc'
    obtain ⟨c, hc, hc''⟩ := Finset.mem_biUnion.1 hc'
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hc''
    refine ⟨ht₁ c b' hb', ?_⟩
    intro E' g hg

    obtain ⟨Ec, gc, hgc, mgc, agc, lgc, lgc'⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B (Localization.Away c)) E
    obtain ⟨Xc, θc, hXc⟩ := H c hc Ec ⟨gc, hgc, mgc, agc, lgc⟩

    have hcu : IsUnit (algebraMap B (Localization.Away (c * b')) c) := by
      have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (c * b')) (c * b')
      rw [map_mul] at h
      exact isUnit_of_mul_isUnit_left h
    letI inst : Algebra (Localization.Away c) (Localization.Away (c * b')) := (IsLocalization.Away.lift c hcu).toAlgebra
    have hφ : (algebraMap (Localization.Away c) (Localization.Away (c * b'))).comp (algebraMap B (Localization.Away c)) =
        algebraMap B (Localization.Away (c * b')) :=
      IsLocalization.Away.lift_comp c hcu
    have hSpec : Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (c * b')))) =
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) (Localization.Away (c * b')))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away c))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
    obtain ⟨hg1, mg, ag, lg⟩ := hg
    have hw : g ≫ E.f = (E'.f ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) (Localization.Away (c * b'))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away c))) := by
      rw [Category.assoc, ← hSpec]; exact hg1.w
    let g' : E'.A ⟶ Ec.A :=
      hgc.lift g (E'.f ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) (Localization.Away (c * b'))))) hw
    have hg'1 : g' ≫ gc = g := hgc.lift_fst _ _ _
    have hg'2 : g' ≫ Ec.f = E'.f ≫ Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) (Localization.Away (c * b')))) :=
      hgc.lift_snd _ _ _
    have hpb : IsPullback g' E'.f Ec.f (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) (Localization.Away (c * b'))))) := by
      refine IsPullback.of_right ?_ hg'2 hgc
      rw [hg'1, ← hSpec]; exact hg1
    have hvia : FakeEllipticCurve.IsPullbackVia (algebraMap (Localization.Away c) (Localization.Away (c * b'))) Ec E' g' := by
      refine ⟨hpb, ?_, ?_, ?_⟩
      · intro T t' P Q
        apply hgc.hom_ext
        · rw [Category.assoc, hg'1, mg t' P Q, mgc]
          exact mul_val_congr E.L (by rw [Category.assoc, ← hSpec]) _ _ _ _
            (show P.1 ≫ g = (P.1 ≫ g') ≫ gc by rw [Category.assoc, hg'1])
            (show Q.1 ≫ g = (Q.1 ≫ g') ≫ gc by rw [Category.assoc, hg'1])
        · rw [Category.assoc, hg'2, ← Category.assoc, (E'.L.mul t' P Q).2, (Ec.L.mul _ _ _).2]
      · intro x
        apply hgc.hom_ext
        · rw [Category.assoc, hg'1, ag x, Category.assoc, agc x, ← Category.assoc, hg'1]
        · rw [Category.assoc, Category.assoc, Ec.act_over, hg'2, ← Category.assoc, E'.act_over]
      · intro T t' P hP
        obtain ⟨P₁, hP₁⟩ := lg t' P hP
        exact lgc' _ ⟨P.1 ≫ g', by rw [Category.assoc, hg'2, ← Category.assoc, P.2]⟩
          ⟨P₁, show P₁ ≫ E.lev = (P.1 ≫ g') ≫ gc by rw [hP₁, Category.assoc, hg'1]⟩
    obtain ⟨θ', hθ', -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
        (Localization.Away c) (Localization.Away (c * b')) Ec E' g' hvia Xc θc hXc
    exact ⟨_, θ', hθ'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia (solution)
