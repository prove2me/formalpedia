-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isFormalModuleVia_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d7f0d1fc-ebb3-5fe8-afe3-36ce761f4048

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isPullbackVia_isFormalModuleVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_comp
import Theorems.Thm_IsLocalization_Away_exists_span_range_mul_eq_top_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isFormalModuleVia_pair
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField

namespace CommonCoordCover

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst h
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

theorem specMap_id (R : Type) [CommRing R] : Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem isPullbackVia_id {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) : FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by
  have hsq : IsPullback (𝟙 E.A) E.f E.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    rw [specMap_id]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨hsq, ?_, ?_, ?_⟩
  · intro T t' P Q
    rw [Category.comp_id]
    exact mul_val_congr E.L (by rw [specMap_id, Category.comp_id]) _ _ _ _ (by simp) (by simp)
  · intro x; simp
  · intro T t' P hP
    obtain ⟨P₀, h⟩ := hP
    exact ⟨P₀, by rw [Category.comp_id]; exact h⟩

theorem idem_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : ∀ x : R, IsIdempotentElem x → x = 0 ∨ x = 1) : ∀ y : S, IsIdempotentElem y → y = 0 ∨ y = 1 := by
  intro y hy
  have hy' : IsIdempotentElem (e.symm y) := hy.map e.symm.toRingHom.toMonoidHom
  rcases h _ hy' with h0 | h1
  · left; rw [← e.apply_symm_apply y, h0, map_zero]
  · right; rw [← e.apply_symm_apply y, h1, map_one]

end CommonCoordCover

open CommonCoordCover in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] [IsNoetherianRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E E' : FakeEllipticCurve Λ N B) :
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L],
        (∀ e : L, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (∀ (E₁ : FakeEllipticCurve Λ N L) (g : E₁.A ⟶ E.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B L) E E₁ g →
            ∃ (X : FormalODModule q L) (θ : RelativeGroupLaw.FormalCoordinates E₁.f 2), E₁.IsFormalModuleVia coord X θ) ∧
        (∀ (E₁' : FakeEllipticCurve Λ N L) (g' : E₁'.A ⟶ E'.A),
            FakeEllipticCurve.IsPullbackVia (algebraMap B L) E' E₁' g' →
            ∃ (X' : FormalODModule q L) (θ' : RelativeGroupLaw.FormalCoordinates E₁'.f 2), E₁'.IsFormalModuleVia coord X' θ') := by
  classical

  obtain ⟨s, hs, hsP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isPullbackVia_isFormalModuleVia coord hcoord B hq E
  set n : ℕ := s.card with hn
  let c : Fin n → B := fun i => (s.equivFin.symm i : B)
  have hc_mem : ∀ i, c i ∈ s := fun i => (s.equivFin.symm i).2
  have hc_span : Ideal.span (Set.range c) = ⊤ := by
    rw [← hs]; congr 1; ext x
    constructor
    · rintro ⟨i, rfl⟩; exact hc_mem i
    · intro hx; exact ⟨s.equivFin ⟨x, hx⟩, by simp [c]⟩

  haveI hNoeth : ∀ i, IsNoetherianRing (Localization.Away (c i)) := fun i =>
    IsLocalization.isNoetherianRing (Submonoid.powers (c i)) _ inferInstance
  have hqL : ∀ i, IsNilpotent ((q : ℕ) : Localization.Away (c i)) := fun i => by
    have := hq.map (algebraMap B (Localization.Away (c i))); rwa [map_natCast] at this

  have hE : ∀ i, ∃ (Ei : FakeEllipticCurve Λ N (Localization.Away (c i))) (gi : Ei.A ⟶ E.A),
      FakeEllipticCurve.IsPullbackVia (algebraMap B (Localization.Away (c i))) E Ei gi ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (c i)))) (P : SchemeHomOver t' Ei.f),
        (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ gi) → FactorsThrough Ei.lev P) := by
    intro i
    obtain ⟨Ei, gi, hg, hmul, hact, hlev, hlev'⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B (Localization.Away (c i))) E
    exact ⟨Ei, gi, ⟨hg, hmul, hact, hlev⟩, hlev'⟩
  choose Ei gEi hEi hlevEi using hE
  have hE' : ∀ i, ∃ (Ei : FakeEllipticCurve Λ N (Localization.Away (c i))) (gi : Ei.A ⟶ E'.A),
      FakeEllipticCurve.IsPullbackVia (algebraMap B (Localization.Away (c i))) E' Ei gi ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (c i)))) (P : SchemeHomOver t' Ei.f),
        (∃ P₀ : T ⟶ E'.C, P₀ ≫ E'.lev = P.1 ≫ gi) → FactorsThrough Ei.lev P) := by
    intro i
    obtain ⟨Ei, gi, hg, hmul, hact, hlev, hlev'⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (algebraMap B (Localization.Away (c i))) E'
    exact ⟨Ei, gi, ⟨hg, hmul, hact, hlev⟩, hlev'⟩
  choose E'i gE'i hE'i hlevE'i using hE'

  have hXE : ∀ i, ∃ (X : FormalODModule q (Localization.Away (c i))) (θ : RelativeGroupLaw.FormalCoordinates (Ei i).f 2),
      (Ei i).IsFormalModuleVia coord X θ := fun i => (hsP (c i) (hc_mem i)).2 (Ei i) (gEi i) (hEi i)
  choose XE θE hXE' using hXE

  have h2 : ∀ i, ∃ s' : Finset (Localization.Away (c i)), Ideal.span (s' : Set (Localization.Away (c i))) = ⊤ ∧
      ∀ d ∈ s', (∀ e : Localization.Away d, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (∀ (E₂ : FakeEllipticCurve Λ N (Localization.Away d)) (g₂ : E₂.A ⟶ (E'i i).A),
          FakeEllipticCurve.IsPullbackVia (algebraMap (Localization.Away (c i)) (Localization.Away d)) (E'i i) E₂ g₂ →
          ∃ (X : FormalODModule q (Localization.Away d)) (θ : RelativeGroupLaw.FormalCoordinates E₂.f 2),
            E₂.IsFormalModuleVia coord X θ) := fun i =>
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_cover_connected_isPullbackVia_isFormalModuleVia coord hcoord
      (Localization.Away (c i)) (hqL i) (E'i i)
  choose s' hs' hs'P using h2
  let m : Fin n → ℕ := fun i => (s' i).card
  let g : ∀ i, Fin (m i) → Localization.Away (c i) := fun i k => ((s' i).equivFin.symm k : Localization.Away (c i))
  have hg_mem : ∀ i k, g i k ∈ s' i := fun i k => ((s' i).equivFin.symm k).2
  have hg_span : ∀ i, Ideal.span (Set.range (g i)) = ⊤ := by
    intro i
    rw [← hs' i]; congr 1; ext x
    constructor
    · rintro ⟨k, rfl⟩; exact hg_mem i k
    · intro hx; exact ⟨(s' i).equivFin ⟨x, hx⟩, by simp [g]⟩

  obtain ⟨bb, ee, hbb, hspan⟩ :=
    IsLocalization.Away.exists_span_range_mul_eq_top_of_span_eq_top c hc_span (fun i => Localization.Away (c i)) m g hg_span

  let σ := (Σ i : Fin n, Fin (m i))
  let eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  refine ⟨Fintype.card σ, fun j => c (eσ.symm j).1 * bb (eσ.symm j).1 (eσ.symm j).2, ?_, ?_⟩
  · rw [← hspan]
    congr 1
    exact (eσ.symm.surjective.range_comp (fun ik : σ => c ik.1 * bb ik.1 ik.2))
  intro j L _ _ hL

  set i : Fin n := (eσ.symm j).1 with hi
  set k : Fin (m i) := (eσ.symm j).2 with hk
  change IsLocalization.Away (c i * bb i k) L at hL

  have hcu : IsUnit (algebraMap B L (c i)) := IsLocalization.Away.isUnit_of_dvd (c i * bb i k) (Dvd.intro _ rfl)
  letI algL : Algebra (Localization.Away (c i)) L := (IsLocalization.Away.lift (c i) hcu).toAlgebra
  haveI towL : IsScalarTower B (Localization.Away (c i)) L :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.Away.lift_eq (c i) hcu x).symm)

  have hassoc : Associated (algebraMap B (Localization.Away (c i)) (bb i k)) (g i k) := by
    have hu : IsUnit (algebraMap B (Localization.Away (c i)) (c i) ^ (ee i k)) :=
      (IsLocalization.Away.algebraMap_isUnit (c i)).pow _
    obtain ⟨u, hu'⟩ := hu
    exact Associated.symm ⟨u, by rw [hu', ← hbb i k]⟩
  haveI hT₀ : IsLocalization.Away (c i * bb i k) (Localization.Away (g i k)) :=
    IsLocalization.Away.mul_of_associated (c i) (bb i k) (g i k) (S := Localization.Away (c i)) hassoc
  let e₀ : Localization.Away (g i k) ≃ₐ[B] L :=
    IsLocalization.algEquiv (Submonoid.powers (c i * bb i k)) (Localization.Away (g i k)) L

  have he₀ : (e₀ : Localization.Away (g i k) →+* L).comp (algebraMap (Localization.Away (c i)) (Localization.Away (g i k))) =
      algebraMap (Localization.Away (c i)) L := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (c i))
    ext x
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B (Localization.Away (c i))]
    exact e₀.commutes x
  obtain ⟨hconn, hcoord2⟩ := hs'P i (g i k) (hg_mem i k)
  refine ⟨idem_of_ringEquiv e₀.toRingEquiv hconn, ?_, ?_⟩
  ·
    intro E₁ g₁ hg₁
    obtain ⟨g'', -, -, -, hg''⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
        (algebraMap B (Localization.Away (c i))) (algebraMap (Localization.Away (c i)) L) (algebraMap B L)
        (RingHom.ext fun x => (IsScalarTower.algebraMap_apply B (Localization.Away (c i)) L x).symm)
        E (Ei i) E₁ (gEi i) (hEi i) (fun t' P => hlevEi i t' P) g₁ hg₁
    obtain ⟨θ', hθ', -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
        (Localization.Away (c i)) L (Ei i) E₁ g'' hg'' (XE i) (θE i) (hXE' i)
    exact ⟨_, θ', hθ'⟩
  ·
    intro E₁' g₁' hg₁'

    obtain ⟨E₂, k₂, hk₂, hmul₂, hact₂, hlev₂, hlev₂'⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (e₀.symm : L →+* Localization.Away (g i k)) E₁'
    have hk₂via : FakeEllipticCurve.IsPullbackVia (e₀.symm : L →+* Localization.Away (g i k)) E₁' E₂ k₂ :=
      ⟨hk₂, hmul₂, hact₂, hlev₂⟩

    have hcompB : ((e₀.symm : L →+* Localization.Away (g i k)).comp (algebraMap B L)) =
        algebraMap B (Localization.Away (g i k)) := RingHom.ext fun x => e₀.symm.commutes x
    have hE₂ : FakeEllipticCurve.IsPullbackVia (algebraMap B (Localization.Away (g i k))) E' E₂ (k₂ ≫ g₁') := by
      have := CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.comp (algebraMap B L)
        (e₀.symm : L →+* Localization.Away (g i k)) E' E₁' E₂ g₁' k₂ hg₁' hk₂via
      rwa [hcompB] at this

    obtain ⟨g₂'', -, -, -, hg₂''⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
        (algebraMap B (Localization.Away (c i))) (algebraMap (Localization.Away (c i)) (Localization.Away (g i k)))
        (algebraMap B (Localization.Away (g i k)))
        (RingHom.ext fun x => (IsScalarTower.algebraMap_apply B (Localization.Away (c i)) (Localization.Away (g i k)) x).symm)
        E' (E'i i) E₂ (gE'i i) (hE'i i) (fun t' P => hlevE'i i t' P) (k₂ ≫ g₁') hE₂
    obtain ⟨X₂, θ₂, hX₂⟩ := hcoord2 E₂ g₂'' hg₂''

    obtain ⟨jj, -, -, -, hjj⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
        (e₀.symm : L →+* Localization.Away (g i k)) (e₀ : Localization.Away (g i k) →+* L) (RingHom.id L)
        (RingHom.ext fun x => e₀.apply_symm_apply x)
        E₁' E₂ E₁' k₂ hk₂via (fun t' P => hlev₂' t' P) (𝟙 _) (isPullbackVia_id E₁')
    letI algT : Algebra (Localization.Away (g i k)) L := (e₀ : Localization.Away (g i k) →+* L).toAlgebra
    obtain ⟨θ', hθ', -⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
        (Localization.Away (g i k)) L E₂ E₁' jj hjj X₂ θ₂ hX₂
    exact ⟨_, θ', hθ'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isFormalModuleVia_pair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_cover_connected_isFormalModuleVia_pair (solution)
