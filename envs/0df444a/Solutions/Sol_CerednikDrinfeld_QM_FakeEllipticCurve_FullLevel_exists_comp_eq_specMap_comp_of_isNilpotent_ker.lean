-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8eea5b7b-5ad2-5fa8-af3f-d2ddd90ec1b3

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

universe u

noncomputable section

namespace LevelExtBody

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : SchemeHomOver s' f :=
  ⟨P.1, P.2.trans h⟩

@[scoped simp] theorem castPt_coe {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s f) : (castPt h P).1 = P.1 := rfl

theorem castPt_injective {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') {P Q : SchemeHomOver s f} (hPQ : castPt h P = castPt h Q) :
    P = Q :=
  Subtype.ext (by simpa [castPt] using congrArg Subtype.val hPQ)

theorem castPt_castPt_symm {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P : SchemeHomOver s' f) :
    castPt h (castPt h.symm P) = P :=
  Subtype.ext rfl

theorem mul_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (P Q : SchemeHomOver s f) :
    L.mul s' (castPt h P) (castPt h Q) = castPt h (L.mul s P Q) := by
  subst h; rfl

theorem one_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') :
    L.one s' = castPt h (L.one s) := by
  subst h; rfl

theorem nsmulPt_castPt {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (h : s = s') (n : ℕ) (P : SchemeHomOver s f) :
    nsmulPt L s' n (castPt h P) = castPt h (nsmulPt L s n P) := by
  subst h; rfl

theorem nsmulPt_natural {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x) =
      L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x)
    rw [L.mul_natural t t' ψ hψ, ih]

section Square

variable {S S' : Type u} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
  (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))

def gPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem gPt_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' E'.f) :
    (gPt hg P).1 = P.1 ≫ g := rfl

theorem gPt_injective {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' E'.f}
    (h : gPt hg P = gPt hg Q) : P = Q := by
  apply Subtype.ext
  exact hg.hom_ext (congrArg Subtype.val h) (P.2.trans Q.2.symm)

def liftPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) :
    SchemeHomOver t' E'.f :=
  ⟨hg.lift Q.1 t' Q.2, hg.lift_snd _ _ _⟩

theorem gPt_liftPt {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')}
    (Q : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) E.f) : gPt hg (liftPt hg Q) = Q := by
  apply Subtype.ext
  simp [gPt, liftPt]

variable
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f),
    (E'.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

include hmul

theorem gPt_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' E'.f) :
    gPt hg (E'.L.mul t' P Q) = E.L.mul _ (gPt hg P) (gPt hg Q) :=
  Subtype.ext (hmul t' P Q)

theorem gPt_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    gPt hg (E'.L.one t') = E.L.one _ := by
  letI := E.L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h := gPt_mul hg hmul t' (E'.L.one t') (E'.L.one t')
  rw [E'.L.one_mul] at h
  have : gPt hg (E'.L.one t') * gPt hg (E'.L.one t') = gPt hg (E'.L.one t') * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel this

theorem gPt_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (P : SchemeHomOver t' E'.f) :
    gPt hg (nsmulPt E'.L t' n P) = nsmulPt E.L _ n (gPt hg P) := by
  induction n with
  | zero => exact gPt_one hg hmul t'
  | succ n ih =>
    show gPt hg (E'.L.mul t' (nsmulPt E'.L t' n P) P) = E.L.mul _ (nsmulPt E.L _ n (gPt hg P)) (gPt hg P)
    rw [gPt_mul hg hmul, ih]

omit hmul in
theorem gPt_pushPt (hact : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of S')} (x : ↥Λ) (P : SchemeHomOver t' E'.f) :
    gPt hg (pushPt (E'.act x) (E'.act_over x) P) = pushPt (E.act x) (E.act_over x) (gPt hg P) := by
  apply Subtype.ext
  simp only [gPt_coe, mapPt_coe, Category.assoc, hact x]

end Square

section GeomPoints

variable {S S₀ : Type u} [CommRing S] [CommRing S₀]

theorem geomPoint_comp (p : S →+* S₀) (k : Type u) [Field k] (sk : S₀ →+* k) :
    geomPoint k sk ≫ Spec.map (CommRingCat.ofHom p) = geomPoint k (sk.comp p) := by
  simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ker_le_ker_of_isNilpotent (p : S →+* S₀) (hI : IsNilpotent (RingHom.ker p))
    {k : Type u} [Field k] (sk : S →+* k) : RingHom.ker p ≤ RingHom.ker sk := by
  intro s hs
  obtain ⟨n, hn⟩ := hI
  have hsn : s ^ n ∈ RingHom.ker p ^ n := Ideal.pow_mem_pow hs n
  rw [hn] at hsn
  have hsn0 : s ^ n = 0 := by simpa using hsn
  have : IsNilpotent (sk s) := ⟨n, by rw [← map_pow, hsn0, map_zero]⟩
  exact (RingHom.mem_ker).mpr this.eq_zero

theorem exists_eq_comp_of_isNilpotent (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    {k : Type u} [Field k] (sk : S →+* k) : ∃ sk₀ : S₀ →+* k, sk = sk₀.comp p :=
  ⟨p.liftOfSurjective hp ⟨sk, ker_le_ker_of_isNilpotent p hI sk⟩,
    (p.liftOfSurjective_comp hp ⟨sk, ker_le_ker_of_isNilpotent p hI sk⟩).symm⟩

end GeomPoints

section Transfer

variable {S S₀ : Type u} [CommRing S] [CommRing S₀]
  {E : FakeEllipticCurve Λ N S} {E₀ : FakeEllipticCurve Λ N S₀} {p : S →+* S₀} {g : E₀.A ⟶ E.A}
  (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
    (E₀.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
  (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
  {m : ℕ} (P₀ : E₀.FullLevel m)
  (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
  (hPred : Spec.map (CommRingCat.ofHom p) ≫ P.1 = (P₀.P).1 ≫ g)

include hact hPred in

theorem castPt_gPt_pushPt_sectionAt (k : Type u) [Field k] (sk₀ : S₀ →+* k) (x : ↥Λ) :
    castPt (geomPoint_comp p k sk₀) (gPt hg (pushPt (E₀.act x) (E₀.act_over x) (FakeEllipticCurve.sectionAt P₀.P k sk₀))) =
      pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k (sk₀.comp p)) := by
  apply Subtype.ext
  simp only [castPt_coe, gPt_coe, mapPt_coe, FakeEllipticCurve.sectionAt, schemeHomOverComp_coe, Category.assoc,
    hact x]
  rw [← reassoc_of% hPred, ← geomPoint_comp p k sk₀, Category.assoc]

include hmul in
theorem castPt_gPt_one (k : Type u) [Field k] (sk₀ : S₀ →+* k) :
    castPt (geomPoint_comp p k sk₀) (gPt hg (E₀.L.one (geomPoint k sk₀))) = E.L.one (geomPoint k (sk₀.comp p)) := by
  rw [gPt_one hg hmul, ← one_castPt]

theorem castPt_gPt_injective (k : Type u) [Field k] (sk₀ : S₀ →+* k) (P₁ P₂ : SchemeHomOver (geomPoint k sk₀) E₀.f)
    (h : castPt (geomPoint_comp p k sk₀) (gPt hg P₁) = castPt (geomPoint_comp p k sk₀) (gPt hg P₂)) : P₁ = P₂ :=
  gPt_injective hg (castPt_injective _ h)

include hmul hact hPred in

theorem generates_comp (k : Type u) [Field k] [IsAlgClosed k] (sk₀ : S₀ →+* k)
    (Q : SchemeHomOver (geomPoint k (sk₀.comp p)) E.f)
    (hQ : nsmulPt E.L (geomPoint k (sk₀.comp p)) m Q = E.L.one (geomPoint k (sk₀.comp p))) :
    ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k (sk₀.comp p)) = Q := by
  have hb := geomPoint_comp p k sk₀

  let Q₀ : SchemeHomOver (geomPoint k sk₀) E₀.f := liftPt hg (castPt hb.symm Q)
  have hQ₀ : castPt hb (gPt hg Q₀) = Q := by
    rw [gPt_liftPt, castPt_castPt_symm]
  have hQ₀tors : nsmulPt E₀.L (geomPoint k sk₀) m Q₀ = E₀.L.one (geomPoint k sk₀) := by
    apply castPt_gPt_injective hg k sk₀
    rw [gPt_nsmul hg hmul, ← nsmulPt_castPt, hQ₀, hQ, castPt_gPt_one hg hmul]
  obtain ⟨x, hx⟩ := P₀.generates k sk₀ Q₀ hQ₀tors
  refine ⟨x, ?_⟩
  rw [← castPt_gPt_pushPt_sectionAt hg hact P₀ P hPred k sk₀ x, hx, hQ₀]

include hmul hact hPred in

theorem annihilator_comp (k : Type u) [Field k] [IsAlgClosed k] (sk₀ : S₀ →+* k) (x : ↥Λ) :
    pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k (sk₀.comp p)) = E.L.one (geomPoint k (sk₀.comp p)) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
  rw [← P₀.annihilator k sk₀ x, ← castPt_gPt_pushPt_sectionAt hg hact P₀ P hPred k sk₀ x, ← castPt_gPt_one hg hmul k sk₀]
  exact ⟨fun h => castPt_gPt_injective hg k sk₀ _ _ h, fun h => by rw [h]⟩

end Transfer

section Reduction

variable {S S₀ : Type u} [CommRing S] [CommRing S₀]
  {E : FakeEllipticCurve Λ N S} {E₀ : FakeEllipticCurve Λ N S₀} {p : S →+* S₀} {g : E₀.A ⟶ E.A}
  (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
    (E₀.L.mul t' P Q).1 ≫ g =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

theorem id_comp_specMap : 𝟙 (Spec (CommRingCat.of S₀)) ≫ Spec.map (CommRingCat.ofHom p) = Spec.map (CommRingCat.ofHom p) :=
  Category.id_comp _

def redPt (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S₀))) E₀.f) : SchemeHomOver (Spec.map (CommRingCat.ofHom p)) E.f :=
  castPt id_comp_specMap (gPt hg P₀)

@[scoped simp] theorem redPt_coe (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S₀))) E₀.f) : (redPt hg P₀).1 = P₀.1 ≫ g := rfl

include hmul in
theorem nsmulPt_redPt {m : ℕ} (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S₀))) E₀.f)
    (h : nsmulPt E₀.L (𝟙 (Spec (CommRingCat.of S₀))) m P₀ = E₀.L.one (𝟙 (Spec (CommRingCat.of S₀)))) :
    nsmulPt E.L (Spec.map (CommRingCat.ofHom p)) m (redPt hg P₀) = E.L.one (Spec.map (CommRingCat.ofHom p)) := by
  unfold redPt
  rw [nsmulPt_castPt, ← gPt_nsmul hg hmul, h, gPt_one hg hmul, ← one_castPt]

end Reduction

end LevelExtBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker.LevelExtBody"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker.LevelExtBody"

open LevelExtBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (P₀ : E₀.FullLevel m) :
    ∃ P : E.FullLevel m, (P₀.P).1 ≫ g = Spec.map (CommRingCat.ofHom p) ≫ (P.P).1 := by

  obtain ⟨P, hPtors, hPred⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker E m hm p hp hI
      (redPt hg P₀.P) (nsmulPt_redPt hg hmul P₀.P P₀.torsion)
  rw [redPt_coe] at hPred

  refine ⟨⟨P, hPtors, ?_, ?_⟩, hPred.symm⟩
  · intro k _ _ sk Q hQ
    obtain ⟨sk₀, rfl⟩ := exists_eq_comp_of_isNilpotent p hp hI sk
    exact generates_comp hg hmul hact P₀ P hPred k sk₀ Q hQ
  · intro k _ _ sk x
    obtain ⟨sk₀, rfl⟩ := exists_eq_comp_of_isNilpotent p hp hI sk
    exact annihilator_comp hg hmul hact P₀ P hPred k sk₀ x

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker (solution)
