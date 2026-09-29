-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/282579ab-c759-5d4d-9d7e-0ca50fa824e9

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints
import Theorems.Thm_PadicInt_ringHom_eq_ringHom_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RepOmega

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

abbrev K0 : Type := WittVector p k ⧸ pIdeal p (WittVector p k)

noncomputable def toK0 : ℤ_[p] →+* K0 p k :=
  (Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp
    ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom)

noncomputable scoped instance algebraK0 : Algebra ℤ_[p] (K0 p k) := (toK0 p k).toAlgebra

theorem natCast_K0_eq_zero : (p : K0 p k) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem isNilpotent_algebraMap_K0 : IsNilpotent (algebraMap ℤ_[p] (K0 p k) p) :=
  ⟨1, by rw [pow_one, map_natCast, natCast_K0_eq_zero]⟩

variable {p k}

theorem ker_le {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hp : (p : B) = 0) :
    ∀ a ∈ pIdeal p (WittVector p k), ψ a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  simp [map_mul, map_natCast, hp]

@[reducible] noncomputable def algOfψ {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hp : (p : B) = 0) : Algebra (K0 p k) B :=
  (Ideal.Quotient.lift (pIdeal p (WittVector p k)) ψ (ker_le ψ hp)).toAlgebra

theorem algebraMap_algOfψ_mk {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hp : (p : B) = 0)
    (a : WittVector p k) :
    letI := algOfψ ψ hp
    algebraMap (K0 p k) B (Ideal.Quotient.mk _ a) = ψ a := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem algebraMap_algOfψ_comp_mk {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hp : (p : B) = 0) :
    letI := algOfψ ψ hp
    (algebraMap (K0 p k) B).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))) = ψ :=
  RingHom.ext fun a => algebraMap_algOfψ_mk ψ hp a

theorem isScalarTower_of_isNilpotent {B : Type} [CommRing B] [Algebra ℤ_[p] B] [Algebra (K0 p k) B]
    (hB : IsNilpotent (p : B)) : IsScalarTower ℤ_[p] (K0 p k) B :=
  IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun (PadicInt.ringHom_eq_ringHom_of_isNilpotent p hB (algebraMap ℤ_[p] B)
      ((algebraMap (K0 p k) B).comp (algebraMap ℤ_[p] (K0 p k)))) x

scoped instance mono_spec_mk : Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) :=
  haveI := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) Ideal.Quotient.mk_surjective
  inferInstance

theorem cond_iff {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (K0 p k)))
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hp : (p : B) = 0) (x : Spec (CommRingCat.of B) ⟶ X) :
    letI := algOfψ ψ hp
    (x ≫ f = Scheme.specOver B) ↔
      (x ≫ f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) =
        Spec.map (CommRingCat.ofHom ψ)) := by
  letI := algOfψ ψ hp
  have key : Scheme.specOver (𝒪 := K0 p k) B ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ) := by
    rw [Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, algebraMap_algOfψ_comp_mk]
  constructor
  · intro h; rw [← Category.assoc, h, key]
  · intro h
    rw [← key, ← Category.assoc] at h
    exact (cancel_mono _).mp h

noncomputable def eYOf {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of (K0 p k))}
    (pt : ∀ (S : Type) [CommRing S] [Algebra (K0 p k) S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] (K0 p k) S],
        (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
    (B : Type) [CommRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (hp : (p : B) = 0) :
    {x : Spec (CommRingCat.of B) ⟶ X //
        x ≫ f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) =
          Spec.map (CommRingCat.ofHom ψ)} ≃ OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B :=
  letI := algOfψ ψ hp
  haveI := isScalarTower_of_isNilpotent (p := p) (k := k) hB
  ((pt B).trans (Equiv.subtypeEquivRight fun x => cond_iff f ψ hp x)).symm

theorem eYOf_symm_val {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of (K0 p k))}
    (pt : ∀ (S : Type) [CommRing S] [Algebra (K0 p k) S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] (K0 p k) S],
        (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
    (B : Type) [CommRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (hp : (p : B) = 0)
    (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) :
    ((eYOf pt B ψ hB hp).symm d).1 =
      (@pt B _ (algOfψ ψ hp) _ (@isScalarTower_of_isNilpotent p _ k _ _ B _ _ (algOfψ ψ hp) hB) d).1 := rfl

end RepOmega
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing.RepOmega"

open RepOmega in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    :
    ∃ (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k)))) (_ : LocallyOfFiniteType πY)
      (_ : IsSeparated πY) (_ : IsReduced Y)
      (eY : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), (p : B) = 0 →
        ({x : Spec (CommRingCat.of B) ⟶ Y // x ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)} ≃ OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)),
      ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
        (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hp : (p : B) = 0) (hp' : (p : B') = 0)
        (g : B →ₐ[ℤ_[p]] B') (hg : (g : B →+* B').comp ψ = ψ')
        (y : {x : Spec (CommRingCat.of B) ⟶ Y // x ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)}),
        eY B' ψ' hB' hp' ⟨Spec.map (CommRingCat.ofHom (g : B →+* B')) ≫ y.1, by
            rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]⟩ =
          DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) g (eY B ψ hB hp y) := by
  obtain ⟨X, f, pt, j, hpt, hjo, hjf, hcov⟩ :=
    CerednikDrinfeld.FormalOmega.Omega.exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing p (K0 p k)
      (isNilpotent_algebraMap_K0 p k)
  obtain ⟨hft, hred⟩ := CerednikDrinfeld.FormalOmega.finiteType_and_isReduced_tensorProduct_chartERing_of_isAlgClosed p k
  have hcov' : ∀ x : X, ∃ γ y, (j γ).base y = x := fun x => by
    obtain ⟨γ, y, hy⟩ := hcov x; exact ⟨γ, y, hy⟩

  have lft : LocallyOfFiniteType f := by
    let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers (Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
      (fun _ => Spec (CommRingCat.of (K0 p k ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p))) j hcov' hjo
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) 𝒰 fun γ => ?_
    show LocallyOfFiniteType (j γ ≫ f)
    rw [hjf γ]
    refine HasRingHomProperty.Spec_iff.mpr ?_
    simp only [CommRingCat.hom_ofHom]
    have : (Algebra.TensorProduct.includeLeftRingHom :
        K0 p k →+* K0 p k ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p) = algebraMap _ _ := RingHom.ext fun _ => rfl
    rw [this, RingHom.finiteType_algebraMap]
    exact hft

  have red : IsReduced X := by
    haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      obtain ⟨γ, y, rfl⟩ := hcov' x
      exact isReduced_of_injective ((j γ).stalkMap y).hom
        (asIso ((j γ).stalkMap y)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X
  have sep : IsSeparated f :=
    CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints p (K0 p k) X f pt hpt
  refine ⟨X, f, lft, sep, red, fun B _ _ _ ψ hB hp => eYOf pt B ψ hB hp, ?_⟩
  intro B B' _ _ _ _ _ _ ψ ψ' hB hB' hp hp' g hg y
  letI iB := algOfψ ψ hp
  letI iB' := algOfψ ψ' hp'
  haveI := isScalarTower_of_isNilpotent (p := p) (k := k) (B := B) hB
  haveI := isScalarTower_of_isNilpotent (p := p) (k := k) (B := B') hB'

  have hcomm : ∀ c : K0 p k, g (algebraMap (K0 p k) B c) = algebraMap (K0 p k) B' c := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [algebraMap_algOfψ_mk, algebraMap_algOfψ_mk]
    exact RingHom.congr_fun hg a
  let gK : B →ₐ[K0 p k] B' := ⟨(g : B →+* B'), hcomm⟩
  have hres : gK.restrictScalars ℤ_[p] = g := AlgHom.ext fun _ => rfl
  obtain ⟨d, rfl⟩ : ∃ d, y = (eYOf pt B ψ hB hp).symm d :=
    ⟨eYOf pt B ψ hB hp y, ((eYOf pt B ψ hB hp).symm_apply_apply y).symm⟩
  rw [Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq_symm_apply]
  apply Subtype.ext
  show Spec.map (CommRingCat.ofHom (g : B →+* B')) ≫ ((eYOf pt B ψ hB hp).symm d).1 =
    ((eYOf pt B' ψ' hB' hp').symm (DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) g d)).1
  rw [eYOf_symm_val, eYOf_symm_val]
  have := congrArg Subtype.val (hpt B B' gK d)
  rw [Scheme.nilpPoints_map_val, hres] at this
  exact this.symm

end S_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing (solution)
