-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/aa2c206b-6c6d-5648-b34f-3ec3ff575500

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_represents_of_zariskiSheaf_of_openAffineCover
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_isOpen_setOf_edgeNondegAt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isPullback_inEdgeChart_of_isLocalRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_map_iff_edgeNondegAt_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open scoped PadicInt Padic TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega
open CategoryTheory AlgebraicGeometry

namespace RepCore
namespace SpecPts

theorem preimage_comp_algebraMap (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T] [Algebra C A]
    (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A) :
    (Spec.preimage y.1).hom.comp (algebraMap C T) = algebraMap C A := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap C T) ≫ Spec.preimage y.1) =
      Spec.map (CommRingCat.ofHom (algebraMap C A)) := by
    rw [Spec.map_comp, Spec.map_preimage]
    exact y.2
  have h2 := Spec.map_injective h
  have h3 := congrArg CommRingCat.Hom.hom h2
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h3
  exact h3

private noncomputable def _root_.RepCore.SpecPts.toAlgHom (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T] [Algebra C A]
    (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A) : T →ₐ[C] A :=
  { toRingHom := (Spec.preimage y.1).hom
    commutes' := fun c => by
      have := RingHom.congr_fun (preimage_comp_algebraMap C T A y) c
      rw [RingHom.comp_apply] at this
      exact this }

p2m_export "RepCore.SpecPts" "toAlgHom"
theorem toAlgHom_toRingHom (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T] [Algebra C A]
    (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A) :
    (toAlgHom C T A y).toRingHom = (Spec.preimage y.1).hom := rfl

noncomputable def ofAlgHom (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T] [Algebra C A]
    (h : T →ₐ[C] A) : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A :=
  ⟨Spec.map (CommRingCat.ofHom h.toRingHom), Scheme.specMap_algHom_comp_specOver h⟩

noncomputable def specAlgEquiv (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T] [Algebra C A] :
    (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A ≃ (T →ₐ[C] A) where
  toFun := toAlgHom C T A
  invFun := ofAlgHom C T A
  left_inv y := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom (toAlgHom C T A y).toRingHom) = y.1
    rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv h := by
    apply AlgHom.coe_ringHom_injective
    show (toAlgHom C T A (ofAlgHom C T A h) : T →+* A) = (h : T →+* A)
    rw [← AlgHom.toRingHom_eq_coe, toAlgHom_toRingHom]
    show (Spec.preimage (Spec.map (CommRingCat.ofHom h.toRingHom))).hom = (h : T →+* A)
    rw [Spec.preimage_map, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe]

theorem specAlgEquiv_symm_val (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T] [Algebra C A]
    (h : T →ₐ[C] A) :
    ((specAlgEquiv C T A).symm h).1 = Spec.map (CommRingCat.ofHom h.toRingHom) := rfl

theorem specAlgEquiv_apply_toRingHom (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T]
    [Algebra C A] (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A) :
    (specAlgEquiv C T A y).toRingHom = (Spec.preimage y.1).hom := rfl

theorem specMap_specAlgEquiv (C T A : Type) [CommRing C] [CommRing T] [CommRing A] [Algebra C T]
    [Algebra C A] (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A) :
    Spec.map (CommRingCat.ofHom (specAlgEquiv C T A y).toRingHom) = y.1 := by
  rw [specAlgEquiv_apply_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem specAlgEquiv_natural (C T A A' : Type) [CommRing C] [CommRing T] [CommRing A] [CommRing A']
    [Algebra C T] [Algebra C A] [Algebra C A'] (φ : A →ₐ[C] A')
    (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).obj A) :
    specAlgEquiv C T A' ((Scheme.nilpPoints (Spec.map (CommRingCat.ofHom (algebraMap C T)))).map φ y) =
      φ.comp (specAlgEquiv C T A y) := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  apply Subtype.ext
  rw [Scheme.nilpPoints_map_val, specAlgEquiv_symm_val,
    show (φ.comp (specAlgEquiv C T A y)).toRingHom = φ.toRingHom.comp (specAlgEquiv C T A y).toRingHom from rfl,
    CommRingCat.ofHom_comp, Spec.map_comp, specMap_specAlgEquiv]

end RepCore.SpecPts

namespace RepCore

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [Algebra ℤ_[p] C]

@[reducible] noncomputable def compAlg (A : Type) [CommRing A] [Algebra C A] : Algebra ℤ_[p] A :=
  ((algebraMap C A).comp (algebraMap ℤ_[p] C)).toAlgebra

theorem compTower (A : Type) [CommRing A] [Algebra C A] :
    letI := compAlg p C A; IsScalarTower ℤ_[p] C A :=
  letI := compAlg p C A; IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev F (A : Type) [CommRing A] [Algebra C A] : Type :=
  @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ (compAlg p C A)

noncomputable def res {A B : Type} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B) :
    @AlgHom ℤ_[p] A B _ _ _ (compAlg p C A) (compAlg p C B) :=
  letI := compAlg p C A; letI := compAlg p C B; haveI := compTower p C A; haveI := compTower p C B
  φ.restrictScalars ℤ_[p]

noncomputable def Fmap (A B : Type) [CommRing A] [CommRing B] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B) :
    F p C A → F p C B :=
  @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ (compAlg p C A) B _ (compAlg p C B) (res p C φ)

theorem Fmap_eq {A B : Type} [CommRing A] [CommRing B] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B) (s : F p C A) :
    Fmap p C A B φ s =
      (letI := compAlg p C A; letI := compAlg p C B; haveI := compTower p C A; haveI := compTower p C B
       (Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) s) := rfl

theorem Fmap_id (A : Type) [CommRing A] [Algebra C A] (s : F p C A) : Fmap p C A A (AlgHom.id C A) s = s := by
  letI := compAlg p C A
  have : res p C (AlgHom.id C A) = AlgHom.id ℤ_[p] A := AlgHom.ext fun _ => rfl
  rw [Fmap, this]
  exact (Omega ℚ_[p] (p : ℤ_[p])).map_id s

theorem Fmap_comp (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Algebra C A] [Algebra C B] [Algebra C D]
    (φ : A →ₐ[C] B) (ψ : B →ₐ[C] D) (s : F p C A) :
    Fmap p C A D (ψ.comp φ) s = Fmap p C B D ψ (Fmap p C A B φ s) := by
  letI := compAlg p C A; letI := compAlg p C B; letI := compAlg p C D
  have : res p C (ψ.comp φ) = (res p C ψ).comp (res p C φ) := AlgHom.ext fun _ => rfl
  rw [Fmap, this]
  exact (Omega ℚ_[p] (p : ℤ_[p])).map_comp (res p C φ) (res p C ψ) s

section Transport
variable {p}

theorem mapE_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
    (iA : Algebra ℤ_[p] A) (iB : Algebra ℤ_[p] B) (iD : Algebra ℤ_[p] D)
    (f : @AlgHom ℤ_[p] A B _ _ _ iA iB) (g : @AlgHom ℤ_[p] B D _ _ _ iB iD)
    (d : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA) :
    @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) B _ iB D _ iD g
        (@DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA B _ iB f d) =
      @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA D _ iD (@AlgHom.comp ℤ_[p] A B D _ _ _ _ iA iB iD g f) d :=
  (@AlgFunctor.map_comp ℤ_[p] _ (Omega ℚ_[p] (p : ℤ_[p])) A _ iA B _ iB D _ iD f g d).symm

theorem mapE_id {A : Type} [CommRing A] (iA : Algebra ℤ_[p] A) (d : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA) :
    @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA A _ iA (@AlgHom.id ℤ_[p] A _ _ iA) d = d :=
  @AlgFunctor.map_id ℤ_[p] _ (Omega ℚ_[p] (p : ℤ_[p])) A _ iA d

theorem mapE_congr {A B : Type} [CommRing A] [CommRing B] (iA : Algebra ℤ_[p] A) (iB : Algebra ℤ_[p] B)
    {f g : @AlgHom ℤ_[p] A B _ _ _ iA iB} (h : ∀ a, f a = g a)
    (d : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA) :
    @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA B _ iB f d =
      @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) A _ iA B _ iB g d := by
  have : f = g := @AlgHom.ext ℤ_[p] A B _ _ _ iA iB f g h
  rw [this]

variable (S : Type) [CommRing S] [Algebra C S] [iS : Algebra ℤ_[p] S] [hS : IsScalarTower ℤ_[p] C S]

noncomputable def toComp : @AlgHom ℤ_[p] S S _ _ _ iS (compAlg p C S) :=
  @AlgHom.mk ℤ_[p] S S _ _ _ iS (compAlg p C S) (RingHom.id S)
    (fun r => @IsScalarTower.algebraMap_apply ℤ_[p] C S _ _ _ _ _ iS hS r)

noncomputable def ofComp : @AlgHom ℤ_[p] S S _ _ _ (compAlg p C S) iS :=
  @AlgHom.mk ℤ_[p] S S _ _ _ (compAlg p C S) iS (RingHom.id S)
    (fun r => (@IsScalarTower.algebraMap_apply ℤ_[p] C S _ _ _ _ _ iS hS r).symm)

noncomputable def toF (d : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ iS) : F p C S :=
  @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ iS S _ (compAlg p C S) (toComp C S) d

noncomputable def ofF (s : F p C S) : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ iS :=
  @DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ (compAlg p C S) S _ iS (ofComp C S) s

theorem ofF_toF (d : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ iS) : ofF C S (toF C S d) = d := by
  rw [ofF, toF, mapE_comp]
  exact (mapE_congr iS iS (g := @AlgHom.id ℤ_[p] S _ _ iS) (fun _ => rfl) d).trans (mapE_id iS d)

theorem toF_ofF (s : F p C S) : toF C S (ofF C S s) = s := by
  rw [ofF, toF, mapE_comp]
  exact (mapE_congr (compAlg p C S) (compAlg p C S) (g := @AlgHom.id ℤ_[p] S _ _ (compAlg p C S)) (fun _ => rfl) s).trans
    (mapE_id (compAlg p C S) s)

theorem toF_natural (S' : Type) [CommRing S'] [Algebra C S'] [iS' : Algebra ℤ_[p] S'] [hS' : IsScalarTower ℤ_[p] C S']
    (φ : S →ₐ[C] S') (d : @DeligneDatum ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ iS) :
    toF C S' ((Omega ℚ_[p] (p : ℤ_[p])).map (AlgHom.restrictScalars ℤ_[p] (S := C) φ) d) =
      Fmap p C S S' φ (toF C S d) := by
  show toF C S' (@DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) S _ iS S' _ iS'
    (AlgHom.restrictScalars ℤ_[p] (S := C) φ) d) = _
  rw [toF, toF, Fmap, mapE_comp, mapE_comp]
  exact mapE_congr iS (compAlg p C S') (fun _ => rfl) d

end Transport

section Hyps
variable {p C}

noncomputable def gStd : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] p, 1]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, (Fact.out : p.Prime).ne_zero])

theorem gStd_val : ((gStd (p := p)) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] p, 1] :=
  rfl

noncomputable abbrev Mp (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : FullLattice ℤ_[p] ℚ_[p] :=
  FullLattice.act γ (FullLattice.act (gStd (p := p)) (stdFullLattice ℚ_[p]))
noncomputable abbrev M1 (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) : FullLattice ℤ_[p] ℚ_[p] :=
  FullLattice.act γ (stdFullLattice ℚ_[p])

def P (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (A : Type) [CommRing A] [Algebra C A] (s : F p C A) : Prop :=
  letI := compAlg p C A
  s.InEdgeChart (p : ℤ_[p]) (Mp γ) (M1 γ)

abbrev Se : Type := C ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p

theorem finite_quot : Finite (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  exact Finite.of_equiv _ (Ideal.quotEquivOfEq (PadicInt.maximalIdeal_eq_span_p (p := p))).toEquiv

theorem card_quot : Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) = p := by
  rw [← Nat.card_congr (Ideal.quotEquivOfEq (PadicInt.maximalIdeal_eq_span_p (p := p))).toEquiv]
  show Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

noncomputable def idAlgHom {S : Type} [CommRing S] (i₁ i₂ : Algebra ℤ_[p] S)
    (h : ∀ r, @algebraMap ℤ_[p] S _ _ i₁ r = @algebraMap ℤ_[p] S _ _ i₂ r) : @AlgHom ℤ_[p] S S _ _ _ i₁ i₂ :=
  @AlgHom.mk ℤ_[p] S S _ _ _ i₁ i₂ (RingHom.id S) h

variable (p C)

theorem sheafH : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A),
      Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (s : ∀ i, F p C (B i)),
      (∀ (i j : Fin n) (D : Type) [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower C A D]
          [IsLocalization.Away (f i * f j) D] (ρ₁ : B i →ₐ[A] D) (ρ₂ : B j →ₐ[A] D),
          Fmap p C _ _ (ρ₁.restrictScalars C) (s i) = Fmap p C _ _ (ρ₂.restrictScalars C) (s j)) →
      ∃! s₀ : F p C A, ∀ i, Fmap p C _ _ (IsScalarTower.toAlgHom C A (B i)) s₀ = s i := by
  intro A _ _ n f hf B _ _ _ _ _ s hcompat
  letI iA : Algebra ℤ_[p] A := compAlg p C A
  letI iB : ∀ i, Algebra ℤ_[p] (B i) := fun i => compAlg p C (B i)
  haveI tB : ∀ i, IsScalarTower ℤ_[p] A (B i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply C A (B i) (algebraMap ℤ_[p] C r)
  let ρ₁ : ∀ i j : Fin n, B i →ₐ[A] Localization.Away (f i * f j) := fun i j =>
    ⟨IsLocalization.Away.awayToAwayRight (f i) (f j), IsLocalization.Away.awayToAwayRight_eq (f i) (f j)⟩
  let ρ₂ : ∀ i j : Fin n, B j →ₐ[A] Localization.Away (f i * f j) := fun i j =>
    ⟨IsLocalization.Away.awayToAwayLeft (f j) (f i), IsLocalization.Away.awayToAwayLeft_eq (f j) (f i)⟩
  have hd : ∀ i j, (Omega ℚ_[p] (p : ℤ_[p])).map ((ρ₁ i j).restrictScalars ℤ_[p]) (s i) =
      (Omega ℚ_[p] (p : ℤ_[p])).map ((ρ₂ i j).restrictScalars ℤ_[p]) (s j) := by
    intro i j

    have hh : ∀ r, @algebraMap ℤ_[p] (Localization.Away (f i * f j)) _ _ (compAlg p C _) r =
        algebraMap ℤ_[p] (Localization.Away (f i * f j)) r := fun r => by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] A (Localization.Away (f i * f j))]
      exact IsScalarTower.algebraMap_apply C A (Localization.Away (f i * f j)) (algebraMap ℤ_[p] C r)
    let e := idAlgHom (compAlg p C (Localization.Away (f i * f j))) inferInstance hh
    have h := congrArg (@DeligneDatum.map ℤ_[p] _ ℚ_[p] _ _ (p : ℤ_[p]) _ _ (compAlg p C (Localization.Away (f i * f j)))
      (Localization.Away (f i * f j)) _ inferInstance e) (hcompat i j (Localization.Away (f i * f j)) (ρ₁ i j) (ρ₂ i j))
    rw [Fmap, Fmap, mapE_comp, mapE_comp] at h
    exact (mapE_congr (iB i) _ (fun _ => rfl) (s i)).trans (h.trans (mapE_congr (iB j) _ (fun _ => rfl) (s j)))
  obtain ⟨d₀, hd₀, huniq⟩ := CerednikDrinfeld.FormalOmega.Omega.existsUnique_glue_of_span_eq_top (K := ℚ_[p]) (p : ℤ_[p])
    A f hf B (fun i j => Localization.Away (f i * f j)) ρ₁ ρ₂ s hd
  have hrw : ∀ (e : F p C A) (i : Fin n), Fmap p C A (B i) (IsScalarTower.toAlgHom C A (B i)) e =
      (Omega ℚ_[p] (p : ℤ_[p])).map (IsScalarTower.toAlgHom ℤ_[p] A (B i)) e := fun e i =>
    mapE_congr iA (iB i) (fun _ => rfl) e
  exact ⟨d₀, fun i => (hrw d₀ i).trans (hd₀ i), fun e he => huniq e fun i => (hrw e i).symm.trans (he i)⟩

theorem isOpenH (hC : IsNilpotent (algebraMap ℤ_[p] C p)) : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (A : Type) [CommRing A] [Algebra C A] (s : F p C A),
      ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
        ∀ (B : Type) [CommRing B] [Algebra C B] (φ : A →ₐ[C] B),
          P γ B (Fmap p C A B φ s) ↔ Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U := by
  intro γ A _ _ s
  letI iA : Algebra ℤ_[p] A := compAlg p C A
  have hA : IsNilpotent (algebraMap ℤ_[p] A p) := hC.map (algebraMap C A)
  haveI := finite_quot (p := p)
  refine ⟨{𝔭 | s.EdgeNondegAt (p : ℤ_[p]) 𝔭.asIdeal (Mp γ) (M1 γ)},
    DeligneDatum.isOpen_setOf_edgeNondegAt (K := ℚ_[p]) (p : ℤ_[p]) hA s (Mp γ) (M1 γ), ?_⟩
  intro B _ _ φ
  letI iB : Algebra ℤ_[p] B := compAlg p C B
  have hcomap : ∀ 𝔮 : Ideal B, Ideal.comap (res p C φ) 𝔮 = Ideal.comap φ.toRingHom 𝔮 := fun 𝔮 => Ideal.ext fun _ => Iff.rfl
  constructor
  · intro hP
    rintro _ ⟨𝔮, rfl⟩
    haveI := 𝔮.isPrime
    have h := (DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap (K := ℚ_[p]) (p : ℤ_[p]) (res p C φ) s 𝔮.asIdeal
      (Mp γ) (M1 γ)).mp (hP 𝔮.asIdeal 𝔮.isPrime)
    rw [hcomap] at h
    exact h
  · intro hU 𝔮 h𝔮
    haveI := h𝔮
    have hmem := hU ⟨⟨𝔮, h𝔮⟩, rfl⟩
    refine (DeligneDatum.edgeNondegAt_map_iff_edgeNondegAt_comap (K := ℚ_[p]) (p : ℤ_[p]) (res p C φ) s 𝔮
      (Mp γ) (M1 γ)).mpr ?_
    rw [hcomap]
    exact hmem

noncomputable def ιm [IsNoetherianRing C] (hC : IsNilpotent (algebraMap ℤ_[p] C p)) (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) :=
  haveI := finite_quot (p := p)
  (CerednikDrinfeld.FormalOmega.Omega.exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
    (p : ℤ_[p]) PadicInt.irreducible_p p card_quot C hC gStd gStd_val γ).choose

abbrev NPe (S : Type) [CommRing S] [Algebra C S] : Type :=
  (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : C →+* Se (p := p) (C := C))))).obj S

theorem ιm_spec [IsNoetherianRing C] (hC : IsNilpotent (algebraMap ℤ_[p] C p)) (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) :
    (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
        [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
        (φ : S →ₐ[C] S') (y : NPe p C S),
        ιm p C hC γ S' ((Scheme.nilpPoints (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : C →+* Se (p := p) (C := C))))).map φ y) =
          (Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) (ιm p C hC γ S y)) ∧
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
        Function.Injective (ιm p C hC γ S)) ∧
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
        (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
        DeligneDatum.InEdgeChart (p : ℤ_[p]) d (Mp γ) (M1 γ) ↔ ∃ y : NPe p C S, ιm p C hC γ S y = d) :=
  haveI := finite_quot (p := p)
  (CerednikDrinfeld.FormalOmega.Omega.exists_natural_injective_inEdgeChart_act_iff_spec_tensorProduct_chartERing
    (p : ℤ_[p]) PadicInt.irreducible_p p card_quot C hC gStd gStd_val γ).choose_spec

noncomputable def chartPts [IsNoetherianRing C] (hC : IsNilpotent (algebraMap ℤ_[p] C p))
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (A : Type) [CommRing A] [Algebra C A] :
    (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : C →+* Se (p := p) (C := C))))).obj A ≃ {s : F p C A // P γ A s} :=
  letI := compAlg p C A; haveI := compTower p C A
  Equiv.ofBijective
    (fun y => (⟨ιm p C hC γ A y, ((ιm_spec p C hC γ).2.2 A _).mpr ⟨y, rfl⟩⟩ : {s : F p C A // P γ A s}))
    ⟨fun y y' h => (ιm_spec p C hC γ).2.1 A (congrArg Subtype.val h),
     fun (s : {s : F p C A // P γ A s}) => by
        obtain ⟨y, hy⟩ := ((ιm_spec p C hC γ).2.2 A s.1).mp s.2
        exact ⟨y, Subtype.ext hy⟩⟩

theorem chartPts_apply_val [IsNoetherianRing C] (hC : IsNilpotent (algebraMap ℤ_[p] C p))
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (A : Type) [CommRing A] [Algebra C A]
    (y : (Scheme.nilpPoints (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : C →+* Se (p := p) (C := C))))).obj A) :
    (chartPts p C hC γ A y).1 = (letI := compAlg p C A; haveI := compTower p C A; ιm p C hC γ A y) := rfl

noncomputable def chartH [IsNoetherianRing C] (hC : IsNilpotent (algebraMap ℤ_[p] C p)) :
    ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (A : Type) [CommRing A] [Algebra C A],
      {s : F p C A // P γ A s} ≃ (Se (p := p) (C := C) →ₐ[C] A) :=
  fun γ A _ _ => (chartPts p C hC γ A).symm.trans (RepCore.SpecPts.specAlgEquiv C (Se (p := p) (C := C)) A)

theorem chart_naturalH [IsNoetherianRing C] (hC : IsNilpotent (algebraMap ℤ_[p] C p)) :
    ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (A B : Type) [CommRing A] [CommRing B]
      [Algebra C A] [Algebra C B]
      (φ : A →ₐ[C] B) (s : {s : F p C A // P γ A s}) (h : P γ B (Fmap p C A B φ s.1)),
      chartH p C hC γ B ⟨Fmap p C A B φ s.1, h⟩ = φ.comp (chartH p C hC γ A s) := by
  intro γ A B _ _ _ _ φ s h
  letI := compAlg p C A; letI := compAlg p C B; haveI := compTower p C A; haveI := compTower p C B
  obtain ⟨y, rfl⟩ := (chartPts p C hC γ A).surjective s
  have hB : (chartPts p C hC γ B).symm ⟨Fmap p C A B φ (chartPts p C hC γ A y).1, h⟩ =
      (Scheme.nilpPoints _).map φ y := by
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    show Fmap p C A B φ (ιm p C hC γ A y) = ιm p C hC γ B ((Scheme.nilpPoints _).map φ y)
    rw [(ιm_spec p C hC γ).1 A B φ y]
    rfl
  show RepCore.SpecPts.specAlgEquiv C Se B ((chartPts p C hC γ B).symm ⟨Fmap p C A B φ (chartPts p C hC γ A y).1, h⟩) =
    φ.comp (RepCore.SpecPts.specAlgEquiv C Se A ((chartPts p C hC γ A).symm (chartPts p C hC γ A y)))
  rw [hB, Equiv.symm_apply_apply, RepCore.SpecPts.specAlgEquiv_natural]

theorem coverH (hC : IsNilpotent (algebraMap ℤ_[p] C p)) : ∀ (K : Type) [Field K] [Algebra C K] (s : F p C K), ∃ γ, P γ K s := by
  intro K _ _ s
  letI := compAlg p C K
  have hK : IsNilpotent (algebraMap ℤ_[p] K p) := hC.map (algebraMap C K)
  obtain ⟨h, d', hpd, hd'⟩ := DeligneDatum.exists_isPullback_inEdgeChart_of_isLocalRing (K := ℚ_[p]) (p : ℤ_[p])
    PadicInt.irreducible_p gStd gStd_val K hK s
  exact ⟨h, DeligneDatum.inEdgeChart_act_of_isPullback h hpd hd'⟩

end Hyps

end RepCore

open RepCore in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra ℤ_[p] C] (hC : IsNilpotent (algebraMap ℤ_[p] C p)) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of C))
      (pt : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
        (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
      (j : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] →
        (Spec (CommRingCat.of (C ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p)) ⟶ X)),
      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
          [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
          (φ : S →ₐ[C] S') (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
          pt S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d) = (Scheme.nilpPoints f).map φ (pt S d)) ∧
      (∀ γ, IsOpenImmersion (j γ)) ∧
      (∀ γ, j γ ≫ f = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p))) ∧
      (∀ x : X, ∃ γ, x ∈ Set.range (j γ).base) := by
  obtain ⟨X, f, pt', j, hnat', hjo, hjf, hcov, -⟩ :=
    AlgebraicGeometry.Scheme.exists_represents_of_zariskiSheaf_of_openAffineCover C
      (fun A _ _ => F p C A) (fun A B _ _ _ _ φ => Fmap p C A B φ)
      (fun A _ _ s => Fmap_id p C A s) (fun A B D _ _ _ _ _ _ φ ψ s => Fmap_comp p C A B D φ ψ s)
      (sheafH p C) (Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (fun γ A _ _ s => P γ A s) (isOpenH p C hC)
      (fun _ => Se (p := p) (C := C)) (chartH p C hC) (chart_naturalH p C hC) (coverH p C hC)
  refine ⟨X, f, fun S _ _ _ _ => ⟨fun d => pt' S (toF C S d), fun y => ofF C S ((pt' S).symm y),
      fun d => by simp [ofF_toF], fun y => by simp [toF_ofF]⟩, j, ?_, hjo, hjf, hcov⟩
  intro S S' _ _ _ _ _ _ _ _ φ d
  apply Subtype.ext
  show (pt' S' (toF C S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d))).1 =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt' S (toF C S d)).1
  rw [toF_natural, hnat']

end S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing (solution)
