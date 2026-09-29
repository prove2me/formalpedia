-- Prove2me | solution 1 for CerednikDrinfeld.QM.nonempty_fakeEllipticCurve_one_of_act_of_algHom_matrix_of_trace_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/db377966-24e1-576e-9551-04733d7fbf77

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_CerednikDrinfeld_QM_exists_act_prod_of_algHom_matrix_of_one_mem_of_mul_mem
import Theorems.Thm_CerednikDrinfeld_QM_trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_prodStr
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_nonempty_fakeEllipticCurve_one_of_act_of_algHom_matrix_of_trace_of_charZero
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

noncomputable section

namespace P2mKcProdEngine

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [hx]
    _ = L.one t := L.inv_mul_cancel t x

theorem inv_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : L.inv t (L.one t) = L.one t := by
  have := L.inv_mul_cancel t (L.one t)
  rwa [L.mul_one] at this

theorem nsmulPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    ∀ n : ℕ, nsmulPt L t n (L.one t) = L.one t
  | 0 => rfl
  | n + 1 => by
    show L.mul t (nsmulPt L t n (L.one t)) (L.one t) = L.one t
    rw [nsmulPt_one t n, L.one_mul]

theorem pushPt_one_of_hom (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt φ hφ (L.one t) = L.one t := by
  apply eq_one_of_mul_self
  have h := hhom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  exact h.symm

@[reducible] def unitSection : Spec (CommRingCat.of S) ⟶ A :=
  (L.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem unitSection_comp : unitSection L ≫ f = 𝟙 _ :=
  (L.one (𝟙 (Spec (CommRingCat.of S)))).2

theorem factorsThrough_unitSection_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    FactorsThrough (unitSection L) P ↔ P = L.one t := by
  have hnat : (L.one t).1 = t ≫ unitSection L := by
    have := L.one_natural (𝟙 (Spec (CommRingCat.of S))) t t (Category.comp_id t)
    rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]
  constructor
  · rintro ⟨P₀, hP₀⟩
    have hP₀t : P₀ = t := by
      have := congrArg (· ≫ f) hP₀
      simp only [Category.assoc, unitSection_comp, Category.comp_id] at this
      rw [this, P.2]
    apply Subtype.ext
    rw [hnat, ← hP₀, hP₀t]
  · rintro rfl
    exact ⟨t, hnat.symm⟩

theorem topologicalKrullDim_fibre_eq {K : Type} [Field K] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n g] (e : Spec (CommRingCat.of K) ⟶ X) (s : ↥(Spec (CommRingCat.of K))) :
    topologicalKrullDim ↥(g.base ⁻¹' {s}) = n := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have huniv : g.base ⁻¹' {s} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph]
  haveI : Nonempty X := ⟨e.base (IsLocalRing.closedPoint K)⟩
  exact le_antisymm (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le g n)
    (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim g n)

theorem main
    (k : Type) [Field k] [CharZero k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hLc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (hA1 : SmoothOfRelativeDimension 1 f)
    {H : Type} [Ring H] [Algebra ℚ H] (O : Submodule ℤ H) (hO₁ : (1 : H) ∈ O)
    (hOmul : ∀ x y : H, x ∈ O → y ∈ O → x * y ∈ O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : H) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
      ε ⟨(x : H) * (y : H), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) H)
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (hj_trace : ∀ (F : Type) [Field F] [CharZero F] (χ : ↥O → F),
      (∀ h : (1 : H) ∈ O, χ ⟨1, h⟩ = 1) →
      (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
      (∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
        χ ⟨(x : H) * (y : H), h⟩ = χ x * χ y) →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F)) :
    Nonempty (FakeEllipticCurve Λ 1 k) := by

  have _ := hΛ

  obtain ⟨act, hact, hformula, hhom, hone, hmul, hadd⟩ :=
    CerednikDrinfeld.QM.exists_act_prod_of_algHom_matrix_of_one_mem_of_mul_mem f L hLc O hO₁ hOmul ε hε hε_hom hε_one hε_mul hε_add Λ j hj

  haveI : SmoothOfRelativeDimension 1 f := hA1
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 1) f f hA1
  haveI h2 : SmoothOfRelativeDimension 2 (prodStr f f) :=
    inferInstanceAs (SmoothOfRelativeDimension (1 + 1) (pullback.fst f f ≫ f))

  set L2 : RelativeGroupLaw k (prodStr f f) := L.prod L with hL2
  have hbundle : AbelianSchemePropertyBundle k (prodStr f f) :=
    GoodReductionJacobian.abelianSchemePropertyBundle_prodStr hA hA
  refine ⟨{
    A := pullback f f
    f := prodStr f f
    L := L2
    comm := RelativeGroupLaw.IsCommutative.prod hLc hLc
    bundle := hbundle
    dim_fibre := fun s => topologicalKrullDim_fibre_eq (prodStr f f) 2 (unitSection L2) s
    act := act
    act_over := hact
    act_hom := hhom
    act_one := hone
    act_mul := hmul
    act_add := hadd
    act_trace := ?_
    C := Spec (CommRingCat.of k)
    lev := unitSection L2
    lev_closed := ?_
    lev_sub := ?_
    lev_one := fun t => (factorsThrough_unitSection_iff L2 t _).2 rfl
    lev_torsion := ?_
    lev_stable := ?_
    lev_finite := by rw [unitSection_comp]; infer_instance
    lev_flat := by rw [unitSection_comp]; infer_instance
    lev_finitePresentation := by rw [unitSection_comp]; infer_instance
    lev_rank := ?_
    lev_fibre := ?_ }⟩
  ·
    intro k' _ _ sk V _ _ _ τ hinj hrange hτadd hτsmul m Φ hΦ n hn
    exact CerednikDrinfeld.QM.trace_eq_intCast_of_isTangentVector_prod_of_smoothOfRelativeDimension_one_of_charZero k f L hLc
      hA1 O hO₁ hOmul ε hε hε_hom hε_one hε_mul hε_add Λ j hj hj_trace m (act m) (hact m) (fun t P => hformula m t P)
      k' sk V τ hinj hrange hτadd hτsmul Φ hΦ n hn
  ·
    haveI : IsProper (prodStr f f) := hbundle.proper
    haveI : IsClosedImmersion (unitSection L2 ≫ prodStr f f) := by
      rw [unitSection_comp]; infer_instance
    exact IsClosedImmersion.of_comp (unitSection L2) (prodStr f f)
  · intro T t P Q hP hQ
    rw [factorsThrough_unitSection_iff] at hP hQ ⊢
    rw [factorsThrough_unitSection_iff]
    subst hP; subst hQ
    exact ⟨L2.one_mul t _, inv_one L2 t⟩
  · intro T t P hP
    rw [factorsThrough_unitSection_iff] at hP
    subst hP
    exact nsmulPt_one L2 t 1
  · intro x T t P hP
    rw [factorsThrough_unitSection_iff] at hP ⊢
    subst hP
    exact pushPt_one_of_hom L2 (act x) (hact x) (fun t P Q => hhom x t P Q) t
  · intro s
    rw [unitSection_comp, Scheme.Hom.finrank_eq_one_of_isIso]
    simp
  · intro k' _ _ sk _
    haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
    haveI : Unique (ZMod 1 × ZMod 1) := uniqueOfSubsingleton (0, 0)
    haveI : Unique {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection L2) P} :=
      { default := ⟨L2.one _, (factorsThrough_unitSection_iff L2 _ _).2 rfl⟩
        uniq := fun P => Subtype.ext ((factorsThrough_unitSection_iff L2 _ _).1 P.2) }
    refine ⟨Equiv.ofUnique _ _, fun x y => ?_⟩
    have h1 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ (x + y) :
        {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection L2) P}) :
          SchemeHomOver (geomPoint k' sk) (prodStr f f)) = L2.one _ :=
      (factorsThrough_unitSection_iff L2 _ _).1 (Subtype.prop _)
    have h2 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ x :
        {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection L2) P}) :
          SchemeHomOver (geomPoint k' sk) (prodStr f f)) = L2.one _ :=
      (factorsThrough_unitSection_iff L2 _ _).1 (Subtype.prop _)
    have h3 : ((Equiv.ofUnique (ZMod 1 × ZMod 1) _ y :
        {P : SchemeHomOver (geomPoint k' sk) (prodStr f f) // FactorsThrough (unitSection L2) P}) :
          SchemeHomOver (geomPoint k' sk) (prodStr f f)) = L2.one _ :=
      (factorsThrough_unitSection_iff L2 _ _).1 (Subtype.prop _)
    rw [h1, h2, h3, L2.one_mul]

end P2mKcProdEngine

end

theorem solution
    (k : Type) [Field k] [CharZero k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hLc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f) (hA1 : SmoothOfRelativeDimension 1 f)
    {H : Type} [Ring H] [Algebra ℚ H] (O : Submodule ℤ H) (hO₁ : (1 : H) ∈ O)
    (hOmul : ∀ x y : H, x ∈ O → y ∈ O → x * y ∈ O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : H) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
      ε ⟨(x : H) * (y : H), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) H)
    (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (hj_trace : ∀ (F : Type) [Field F] [CharZero F] (χ : ↥O → F),
      (∀ h : (1 : H) ∈ O, χ ⟨1, h⟩ = 1) →
      (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
      (∀ (x y : ↥O) (h : (x : H) * (y : H) ∈ O),
        χ ⟨(x : H) * (y : H), h⟩ = χ x * χ y) →
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F)) :
    Nonempty (FakeEllipticCurve Λ 1 k) := by
  exact P2mKcProdEngine.main k f L hLc hA hA1 O hO₁ hOmul ε hε hε_hom hε_one hε_mul hε_add Λ hΛ j hj hj_trace

end S_CerednikDrinfeld_QM_nonempty_fakeEllipticCurve_one_of_act_of_algHom_matrix_of_trace_of_charZero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_nonempty_fakeEllipticCurve_one_of_act_of_algHom_matrix_of_trace_of_charZero (solution)
