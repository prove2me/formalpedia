-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/25e71714-2ad3-58b9-8b36-9597e95fda5d

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_ideal_forall_map_eq_iff_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace OmegaSepAux

section Diagonal

universe u

def diagSet {X Y : Scheme.{u}} (f : X ⟶ Y) : Set ↥(pullback f f) :=
  {z | ∃ (K : Type u) (_ : Field K) (g : Spec (CommRingCat.of K) ⟶ pullback f f),
    g ≫ pullback.fst f f = g ≫ pullback.snd f f ∧ z ∈ Set.range g.base}

theorem range_diagonal_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set.range (pullback.diagonal f).base = diagSet f := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨X.residueField x, inferInstance, X.fromSpecResidueField x ≫ pullback.diagonal f, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
    · refine ⟨IsLocalRing.closedPoint (X.residueField x), ?_⟩
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · rintro ⟨K, _, g, hg, ⟨q, rfl⟩⟩
    have : g = (g ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hg]
    refine ⟨(g ≫ pullback.fst f f).base q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← this]

theorem isClosed_of_affineCover {P : Scheme.{u}} (E : Set ↥P)
    (h : ∀ i, IsClosed ((P.affineCover.f i).base ⁻¹' E)) : IsClosed E := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨y, hy⟩ := P.affineCover.covers z
  refine ⟨(P.affineCover.f (P.affineCover.idx z)).base '' ((P.affineCover.f (P.affineCover.idx z)).base ⁻¹' E)ᶜ,
    ?_, ?_, ⟨y, ?_, hy⟩⟩
  · rintro _ ⟨w, hw, rfl⟩ hwE
    exact hw hwE
  · exact (P.affineCover.f _).isOpenEmbedding.isOpenMap _ (h _).isOpen_compl
  · show (P.affineCover.f (P.affineCover.idx z)) y ∉ E
    rw [hy]; exact hz

end Diagonal

section Chart

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [Algebra ℤ_[p] C]
  (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of C))
  (pt : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
      (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
  (hpt : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
        [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
        (φ : S →ₐ[C] S') (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
        pt S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d) = (Scheme.nilpPoints f).map φ (pt S d))

include hpt in

theorem comp_eq_comp_iff {S : Type} [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
    (a₁ a₂ : (Scheme.nilpPoints f).obj S) (I : Ideal S)
    (hI : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T] (χ : S →ₐ[ℤ_[p]] T),
      ((pt S).symm a₁).map (p : ℤ_[p]) χ = ((pt S).symm a₂).map (p : ℤ_[p]) χ ↔ I ≤ RingHom.ker (χ : S →+* T))
    {T : Type} [CommRing T] (φ : S →+* T) :
    Spec.map (CommRingCat.ofHom φ) ≫ a₁.1 = Spec.map (CommRingCat.ofHom φ) ≫ a₂.1 ↔ I ≤ RingHom.ker φ := by
  letI : Algebra C T := (φ.comp (algebraMap C S)).toAlgebra
  letI : Algebra ℤ_[p] T := (φ.comp (algebraMap ℤ_[p] S)).toAlgebra
  haveI : IsScalarTower ℤ_[p] C T := IsScalarTower.of_algebraMap_eq fun r => by
    show φ (algebraMap ℤ_[p] S r) = φ (algebraMap C S (algebraMap ℤ_[p] C r))
    rw [IsScalarTower.algebraMap_apply ℤ_[p] C S]
  let φC : S →ₐ[C] T := { toRingHom := φ, commutes' := fun c => rfl }
  have hmap : ∀ a : (Scheme.nilpPoints f).obj S,
      ((Scheme.nilpPoints f).map φC a).1 = Spec.map (CommRingCat.ofHom φ) ≫ a.1 := fun a => rfl
  have hI' := hI T (φC.restrictScalars ℤ_[p])
  constructor
  · intro h
    have h1 : (Scheme.nilpPoints f).map φC a₁ = (Scheme.nilpPoints f).map φC a₂ :=
      Subtype.ext (by rw [hmap, hmap, h])
    have h2 : pt T ((Omega ℚ_[p] (p : ℤ_[p])).map (φC.restrictScalars ℤ_[p]) ((pt S).symm a₁)) =
        pt T ((Omega ℚ_[p] (p : ℤ_[p])).map (φC.restrictScalars ℤ_[p]) ((pt S).symm a₂)) := by
      rw [hpt, hpt, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h1]
    exact hI'.mp ((pt T).injective h2)
  · intro h
    have h3 := hI'.mpr h
    have h2 : (Scheme.nilpPoints f).map φC (pt S ((pt S).symm a₁)) =
        (Scheme.nilpPoints f).map φC (pt S ((pt S).symm a₂)) := by
      rw [← hpt, ← hpt]
      exact congrArg (pt T) h3
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
    have := congrArg Subtype.val h2
    rwa [hmap, hmap] at this

include hpt in

theorem isClosed_preimage_diagSet {S : Type} [CommRing S] (j : Spec (CommRingCat.of S) ⟶ pullback f f)
    (hj : IsOpenImmersion j) : IsClosed (j.base ⁻¹' diagSet f) := by
  haveI := hj
  obtain ⟨instC, hC⟩ : ∃ inst : Algebra C S, (j ≫ pullback.fst f f) ≫ f = @Scheme.specOver C _ S _ inst :=
    ⟨(Spec.preimage ((j ≫ pullback.fst f f) ≫ f)).hom.toAlgebra, by
      simp only [Scheme.specOver, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  letI := instC
  letI : Algebra ℤ_[p] S := ((algebraMap C S).comp (algebraMap ℤ_[p] C)).toAlgebra
  haveI : IsScalarTower ℤ_[p] C S := IsScalarTower.of_algebraMap_eq fun r => rfl
  let a₁ : (Scheme.nilpPoints f).obj S := ⟨j ≫ pullback.fst f f, hC⟩
  let a₂ : (Scheme.nilpPoints f).obj S := ⟨j ≫ pullback.snd f f, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hC⟩
  obtain ⟨I, hI⟩ := CerednikDrinfeld.FormalOmega.DeligneDatum.exists_ideal_forall_map_eq_iff_le_ker (p : ℤ_[p])
    ((pt S).symm a₁) ((pt S).symm a₂)
  have key : ∀ (T : Type) [CommRing T] (φ : S →+* T),
      Spec.map (CommRingCat.ofHom φ) ≫ a₁.1 = Spec.map (CommRingCat.ofHom φ) ≫ a₂.1 ↔ I ≤ RingHom.ker φ :=
    fun T _ φ => comp_eq_comp_iff p C X f pt hpt a₁ a₂ I hI φ
  suffices hE : j.base ⁻¹' diagSet f = PrimeSpectrum.zeroLocus (I : Set S) by
    rw [hE]; exact PrimeSpectrum.isClosed_zeroLocus _
  ext 𝔭
  constructor
  · rintro ⟨K, _, g, hg, ⟨q, hq⟩⟩
    have hsub : Set.range g.base ⊆ Set.range j.base := by
      rintro _ ⟨q', rfl⟩
      have : q' = q := PrimeSpectrum.ext
        (by rw [@Ideal.eq_bot_of_prime K _ q.asIdeal q.isPrime, @Ideal.eq_bot_of_prime K _ q'.asIdeal q'.isPrime])
      rw [this]
      exact ⟨𝔭, hq.symm⟩
    obtain ⟨φ', hφ'⟩ := Spec.map_surjective (IsOpenImmersion.lift j g hsub)
    have hg' : Spec.map φ' ≫ j = g := by rw [hφ']; exact IsOpenImmersion.lift_fac j g hsub
    have hφ : Spec.map (CommRingCat.ofHom φ'.hom) = Spec.map φ' := by rw [CommRingCat.ofHom_hom]
    have heq : Spec.map (CommRingCat.ofHom φ'.hom) ≫ a₁.1 = Spec.map (CommRingCat.ofHom φ'.hom) ≫ a₂.1 := by
      show Spec.map (CommRingCat.ofHom φ'.hom) ≫ (j ≫ pullback.fst f f) =
        Spec.map (CommRingCat.ofHom φ'.hom) ≫ (j ≫ pullback.snd f f)
      rw [hφ, ← Category.assoc, ← Category.assoc, hg', hg]
    have hle := (key K φ'.hom).mp heq
    have h𝔭 : 𝔭 = (Spec.map φ').base q :=
      j.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hg']; exact hq.symm)
    show (I : Set S) ⊆ 𝔭.asIdeal
    intro s hs
    rw [h𝔭, Spec.map_apply, PrimeSpectrum.comap_asIdeal, SetLike.mem_coe, Ideal.mem_comap]
    have : φ'.hom s = 0 := hle hs
    rw [this]
    exact zero_mem _
  · intro h𝔭
    let Q : Type := S ⧸ 𝔭.asIdeal
    let K : Type := FractionRing Q
    let φ : S →+* K := (algebraMap Q K).comp (Ideal.Quotient.mk 𝔭.asIdeal)
    have hker : RingHom.ker φ = 𝔭.asIdeal := by
      ext s
      rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective Q K),
        Ideal.Quotient.eq_zero_iff_mem]
    have hle : I ≤ RingHom.ker φ := by rw [hker]; exact h𝔭
    have heq := (key K φ).mpr hle
    refine ⟨K, inferInstance, Spec.map (CommRingCat.ofHom φ) ≫ j, ?_, ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩⟩
    · rw [Category.assoc, Category.assoc]; exact heq
    · show j.base ((Spec.map (CommRingCat.ofHom φ)).base ⟨⊥, Ideal.isPrime_bot⟩) = j.base 𝔭
      congr 1
      apply PrimeSpectrum.ext
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot, hker]

end Chart

end OmegaSepAux

theorem solution
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [Algebra ℤ_[p] C]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of C))
    (pt : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
      (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
    (hpt : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
        [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
        (φ : S →ₐ[C] S') (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
        pt S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d) = (Scheme.nilpPoints f).map φ (pt S d)) :
    IsSeparated f := by
  have hE : IsClosed (Set.range (pullback.diagonal f).base) := by
    rw [OmegaSepAux.range_diagonal_eq f]
    exact OmegaSepAux.isClosed_of_affineCover _ fun i =>
      OmegaSepAux.isClosed_preimage_diagSet p C X f pt hpt _ (inferInstance : IsOpenImmersion ((pullback f f).affineCover.f i))
  haveI : IsClosedImmersion (pullback.diagonal f) := IsClosedImmersion.of_isPreimmersion _ hE
  exact ⟨this⟩

end

end S_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_Omega_isSeparated_of_equiv_nilpPoints (solution)
