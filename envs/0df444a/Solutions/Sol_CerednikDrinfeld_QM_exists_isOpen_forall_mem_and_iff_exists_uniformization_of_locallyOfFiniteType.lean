-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_isOpen_forall_mem_and_iff_exists_uniformization_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ce438c85-e7c3-5d6d-a534-dc258ed0de4a

import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_QM_exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_and_iff_exists_uniformization_of_locallyOfFiniteType
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace OpenImageSpecialFibre

theorem base_comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (f' : Y ⟶ Z) (x : ↥X) : (f ≫ f').base x = f'.base (f.base x) := rfl

theorem spec_field_subsingleton (k : Type) [Field k] : Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

theorem isUnit_natCast_of_not_dvd {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (π : 𝒪) (hπ : Irreducible π) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (m : ℕ) (hm : ¬ r ∣ m) :
    IsUnit ((m : ℕ) : 𝒪) := by
  haveI hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  haveI : Nontrivial (𝒪 ⧸ Ideal.span {π}) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  have hr0 : ((r : ℕ) : 𝒪 ⧸ Ideal.span {π}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem, ← hunr]
    exact Ideal.mem_span_singleton_self _
  haveI : CharP (𝒪 ⧸ Ideal.span {π}) r := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hr0
  rw [← IsLocalRing.notMem_maximalIdeal, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    ← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝒪 ⧸ Ideal.span {π}) r]
  exact hm

section Main

variable {r : ℕ} [Fact r.Prime]
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
variable (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
variable (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
variable (G : Type) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType fM]
variable (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
  (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
variable (hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
    Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))
variable (het : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
    Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
    ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
      ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in

theorem algebraMap_eq_zero (k : Type) [Field k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) : algebraMap 𝒪 k π = 0 :=
  hk.eq_zero

include hπ hres hunr hOnr_max hOnr_alg hnat het in

theorem main :
    ∃ V : Set ↥M, IsOpen V ∧
      ∀ x : ↥M, (x ∈ V ∧ ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π))
          (y : (Scheme.nilpPoints fM).obj k), y.1.base (IsLocalRing.closedPoint k) = x) ↔
        ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π))
          (y : (Scheme.nilpPoints fM).obj k), y.1.base (IsLocalRing.closedPoint k) = x ∧
          ∃ (ψ : Onr →ₐ[𝒪] k) (P : (Omega K₀ π).obj k) (g : G), Θf k hk ((ψ, P), g) = y := by
  classical

  haveI hmax : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
  let k₀ : Type := 𝒪 ⧸ Ideal.span {π}
  letI : Field k₀ := Ideal.Quotient.field (Ideal.span {π})

  let I : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π}
  haveI : I.IsMaximal := hOnr_max
  let kb : Type := Onr ⧸ I
  letI : Field kb := Ideal.Quotient.field I
  have hkbπ : algebraMap 𝒪 kb π = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪 Onr kb, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hkb : IsNilpotent (algebraMap 𝒪 kb π) := ⟨1, by rw [pow_one, hkbπ]⟩
  let ψ₀ : Onr →ₐ[𝒪] kb := Ideal.Quotient.mkₐ 𝒪 I

  let lam : k₀ →+* kb := Ideal.Quotient.lift (Ideal.span {π}) (algebraMap 𝒪 kb) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hkbπ, mul_zero])
  have hlam : lam.comp (algebraMap 𝒪 k₀) = algebraMap 𝒪 kb := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.lift_mk _ _ _

  let s₀ : Spec (CommRingCat.of k₀) ⟶ Spec (CommRingCat.of 𝒪) := Scheme.specOver k₀
  haveI : IsClosedImmersion s₀ := by
    refine IsClosedImmersion.spec_of_surjective _ ?_
    show Function.Surjective (algebraMap 𝒪 k₀)
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  let ι : pullback fM s₀ ⟶ M := pullback.fst fM s₀
  let q₀ : pullback fM s₀ ⟶ Spec (CommRingCat.of k₀) := pullback.snd fM s₀
  haveI : IsClosedImmersion ι := MorphismProperty.pullback_fst _ _ inferInstance

  let b : Spec (CommRingCat.of kb) ⟶ Spec (CommRingCat.of k₀) := Spec.map (CommRingCat.ofHom lam)
  haveI : Subsingleton ↥(Spec (CommRingCat.of k₀)) := spec_field_subsingleton k₀
  haveI : UniversallyOpen b := inferInstance
  let f₁ : pullback q₀ b ⟶ pullback fM s₀ := pullback.fst q₀ b
  let p₂ : pullback q₀ b ⟶ Spec (CommRingCat.of kb) := pullback.snd q₀ b
  let p₁ : pullback q₀ b ⟶ M := f₁ ≫ ι
  have hb : b ≫ s₀ = Scheme.specOver kb := by
    show Spec.map (CommRingCat.ofHom lam) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 kb))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hlam]
  have hN : IsPullback p₁ p₂ fM (Scheme.specOver kb) := by
    have hsq := (IsPullback.of_hasPullback q₀ b).paste_horiz (IsPullback.of_hasPullback fM s₀)
    rwa [hb] at hsq

  obtain ⟨W, hWo, hW⟩ :=
    CerednikDrinfeld.QM.exists_isOpen_forall_mem_iff_exists_uniformization_of_isPullback 𝒪 inferInstance π hπ hres hunr K₀ Onr
      hOnr_max hOnr_alg G M fM Θf hnat het kb hkb ψ₀ (pullback q₀ b) p₁ p₂ hN

  have hf₁W : IsOpen (f₁.base '' W) := f₁.isOpenMap _ hWo
  obtain ⟨V, hVo, hVW⟩ := (Scheme.Hom.isClosedEmbedding ι).isInducing.isOpen_iff.mp hf₁W
  refine ⟨V, hVo, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hxV, k, _, _, _, hk, y, hy⟩

    have hkπ : algebraMap 𝒪 k π = 0 := hk.eq_zero
    let lamk : k₀ →+* k := Ideal.Quotient.lift (Ideal.span {π}) (algebraMap 𝒪 k) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hkπ, mul_zero])
    have hlamk : lamk.comp (algebraMap 𝒪 k₀) = algebraMap 𝒪 k := by
      refine RingHom.ext fun a => ?_
      rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.lift_mk _ _ _
    have hw : y.1 ≫ fM = Spec.map (CommRingCat.ofHom lamk) ≫ s₀ := by
      rw [y.2]
      show Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) =
        Spec.map (CommRingCat.ofHom lamk) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k₀))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hlamk]
    let m₀ : Spec (CommRingCat.of k) ⟶ pullback fM s₀ := pullback.lift y.1 (Spec.map (CommRingCat.ofHom lamk)) hw
    have hm₀ : ι.base (m₀.base (IsLocalRing.closedPoint k)) = x := by
      rw [← base_comp_apply, pullback.lift_fst]
      exact hy

    have hmem : m₀.base (IsLocalRing.closedPoint k) ∈ f₁.base '' W := by
      rw [← hVW]
      show ι.base (m₀.base (IsLocalRing.closedPoint k)) ∈ V
      rw [hm₀]
      exact hxV
    obtain ⟨n, hnW, hn⟩ := hmem
    obtain ⟨k₁, _, _, hk₁, φ, z, hz₂, hzn, P, g, hΘ⟩ := (hW n).mp hnW

    let k₂ : Type := AlgebraicClosure k₁
    let e : k₁ →ₐ[𝒪] k₂ := IsScalarTower.toAlgHom 𝒪 k₁ k₂
    have hk₂ : IsNilpotent (algebraMap 𝒪 k₂ π) := by
      obtain ⟨m, hm⟩ := hk₁
      exact ⟨m, by rw [IsScalarTower.algebraMap_apply 𝒪 k₁ k₂, ← map_pow, hm, map_zero]⟩
    let X₁ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj k₁ := ((φ.comp ψ₀, P), g)
    let X₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj k₂ :=
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map e X₁
    haveI : Subsingleton ↥(Spec (CommRingCat.of k₁)) := spec_field_subsingleton k₁
    refine ⟨k₂, inferInstance, inferInstance, inferInstance, hk₂, Θf k₂ hk₂ X₂, ?_, X₂.1.1, X₂.1.2, X₂.2, rfl⟩
    have h1 : (Θf k₂ hk₂ X₂).1 = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ z ≫ p₁ := by
      show (Θf k₂ hk₂ ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map e X₁)).1 = _
      rw [hnat k₁ k₂ hk₁ hk₂ e X₁, Scheme.nilpPoints_map_val, hΘ]
    rw [h1, base_comp_apply, base_comp_apply,
      Subsingleton.elim ((Spec.map (CommRingCat.ofHom e.toRingHom)).base (IsLocalRing.closedPoint k₂)) (IsLocalRing.closedPoint k₁),
      hzn]
    show ι.base (f₁.base n) = x
    rw [hn, hm₀]
  · rintro ⟨k, _, _, _, hk, y, hy, ψ, P, g, hΘ⟩
    refine ⟨?_, k, inferInstance, inferInstance, inferInstance, hk, y, hy⟩

    have hkπ : algebraMap 𝒪 k π = 0 := hk.eq_zero
    let φ : kb →ₐ[𝒪] k := Ideal.Quotient.liftₐ I ψ (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, AlgHom.commutes, hkπ, mul_zero])
    have hφψ : φ.comp ψ₀ = ψ := by
      refine AlgHom.ext fun a => ?_
      rfl

    have hw : y.1 ≫ fM = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Scheme.specOver kb := by
      rw [y.2, Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact (φ.comp_algebraMap).symm
    let z : Spec (CommRingCat.of k) ⟶ pullback q₀ b := hN.lift y.1 (Spec.map (CommRingCat.ofHom φ.toRingHom)) hw
    have hz₁ : z ≫ p₁ = y.1 := hN.lift_fst _ _ _
    have hz₂ : z ≫ p₂ = Spec.map (CommRingCat.ofHom φ.toRingHom) := hN.lift_snd _ _ _
    have hX : ((φ.comp ψ₀, P), g) =
        (((ψ, P), g) : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj k) := by
      rw [hφψ]
      rfl
    have hnW : z.base (IsLocalRing.closedPoint k) ∈ W := by
      refine (hW _).mpr ⟨k, inferInstance, inferInstance, hk, φ, z, hz₂, rfl, P, g, ?_⟩
      rw [hz₁, ← hΘ]
      exact congrArg (fun X => (Θf k hk X).1) hX

    have hmem : f₁.base (z.base (IsLocalRing.closedPoint k)) ∈ ι.base ⁻¹' V := by
      rw [hVW]
      exact ⟨_, hnW, rfl⟩
    have hx : ι.base (f₁.base (z.base (IsLocalRing.closedPoint k))) = x := by
      rw [← base_comp_apply, ← base_comp_apply]
      show (z ≫ p₁).base (IsLocalRing.closedPoint k) = x
      rw [hz₁]
      exact hy
    rw [← hx]
    exact hmem

end Main

end OpenImageSpecialFibre

theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (G : Type)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType fM]
    (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
    (hnat :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))
    (het :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y) :
    ∃ V : Set ↥M, IsOpen V ∧
      ∀ x : ↥M, (x ∈ V ∧ ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π))
          (y : (Scheme.nilpPoints fM).obj k), y.1.base (IsLocalRing.closedPoint k) = x) ↔
        ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra 𝒪 k) (hk : IsNilpotent (algebraMap 𝒪 k π))
          (y : (Scheme.nilpPoints fM).obj k), y.1.base (IsLocalRing.closedPoint k) = x ∧
          ∃ (ψ : Onr →ₐ[𝒪] k) (P : (Omega K₀ π).obj k) (g : G), Θf k hk ((ψ, P), g) = y := by
  haveI := hdvr
  exact OpenImageSpecialFibre.main 𝒪 π hπ hres hunr K₀ Onr hOnr_max hOnr_alg G M fM Θf hnat het

end S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_and_iff_exists_uniformization_of_locallyOfFiniteType
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_isOpen_forall_mem_and_iff_exists_uniformization_of_locallyOfFiniteType (solution)
