-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/91228406-699d-5dbb-8b91-ce69ed2e14b9

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

namespace C1Aux
open CategoryTheory AlgebraicGeometry GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem nilEval_map {B B' C : Type} [CommRing B] [CommRing B'] [CommRing C] [Algebra B C] [Algebra B' C]
    (f : B →+* B') (hf : (algebraMap B' C).comp f = algebraMap B C)
    {σ : Type} [Fintype σ] [DecidableEq σ] (n : ℕ) (p : MvPowerSeries σ B) (a : σ → C) :
    MvFormalGroup.nilEval n (MvPowerSeries.map f p) a = MvFormalGroup.nilEval n p a := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hf]

theorem nilMul_map {B B' C : Type} [CommRing B] [CommRing B'] [CommRing C] [Algebra B C] [Algebra B' C]
    (f : B →+* B') (hf : (algebraMap B' C).comp f = algebraMap B C)
    {g : ℕ} (F : MvFormalGroup g B) (n : ℕ) (s t : Fin g → C) :
    (F.map f).nilMul n s t = F.nilMul n s t := by
  funext i
  exact nilEval_map f hf n (F.toPowerSeries i) (Sum.elim s t)

theorem eq_one_of_mul_self {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.inv_mul_cancel]

theorem mul_base_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  rw [show P = P' from Subtype.ext hP, show Q = Q' from Subtype.ext hQ]

theorem one_base_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst h; rfl

end C1Aux

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    (E : FakeEllipticCurve Λ N B) (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B B') E E' g)
    (X : FormalODModule q B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates E'.f 2, E'.IsFormalModuleVia coord (X.map (algebraMap B B')) θ' ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B' B''] [IsScalarTower B B' B''] (s : Fin 2 → B''),
        (∀ i, IsNilpotent (s i)) → (θ' B'' s).1 ≫ g = (θ B'' s).1 := by
  classical
  obtain ⟨hpb, hmul, hact, hlev⟩ := hg

  have HB : ∀ (C : Type) [CommRing C] [Algebra B' C],
      Scheme.specOver (𝒪 := B') C ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')) =
        Spec.map (CommRingCat.ofHom ((algebraMap B' C).comp (algebraMap B B'))) := by
    intro C _ _
    rw [Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have g_one : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')),
      (E'.L.one t').1 ≫ g = (E.L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')))).1 := by
    intro T t'
    have h := hmul t' (E'.L.one t') (E'.L.one t')
    rw [E'.L.one_mul] at h
    have := C1Aux.eq_one_of_mul_self E.L _ ⟨(E'.L.one t').1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, (E'.L.one t').2]⟩
      (Subtype.ext h.symm)
    exact congrArg Subtype.val this

  let θ' : RelativeGroupLaw.FormalCoordinates E'.f 2 := fun C _ _ s =>
    letI : Algebra B C := ((algebraMap B' C).comp (algebraMap B B')).toAlgebra
    ⟨hpb.lift (θ C s).1 (Scheme.specOver (𝒪 := B') C) (by rw [(θ C s).2, HB]), hpb.lift_snd _ _ _⟩
  have θ'g : ∀ (C : Type) [CommRing C] [Algebra B' C] (s : Fin 2 → C),
      (θ' C s).1 ≫ g = (letI : Algebra B C := ((algebraMap B' C).comp (algebraMap B B')).toAlgebra; (θ C s).1) := by
    intro C _ _ s
    exact hpb.lift_fst _ _ _

  have ext' : ∀ (C : Type) [CommRing C] [Algebra B' C] (P P' : SchemeHomOver (Scheme.specOver (𝒪 := B') C) E'.f),
      P.1 ≫ g = P'.1 ≫ g → P = P' := by
    intro C _ _ P P' h
    exact Subtype.ext (hpb.hom_ext h (P.2.trans P'.2.symm))
  obtain ⟨hnat, hnil⟩ := hX.1
  refine ⟨θ', ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·
    intro C _ _ C' _ _ ψ s hs
    letI iC : Algebra B C := ((algebraMap B' C).comp (algebraMap B B')).toAlgebra
    letI iC' : Algebra B C' := ((algebraMap B' C').comp (algebraMap B B')).toAlgebra
    let ψB : C →ₐ[B] C' :=
      { toRingHom := ψ.toRingHom
        commutes' := fun r => by
          show ψ (algebraMap B' C (algebraMap B B' r)) = algebraMap B' C' (algebraMap B B' r)
          exact ψ.commutes _ }
    have h1 := hnat C C' ψB s hs
    apply ext'
    rw [θ'g, schemeHomOverComp_coe, Category.assoc, θ'g]
    have := congrArg Subtype.val h1
    rw [schemeHomOverComp_coe] at this
    exact this
  ·
    intro C _ _ J n hJ
    letI iC : Algebra B C := ((algebraMap B' C).comp (algebraMap B B')).toAlgebra
    obtain ⟨hinto, hinj, honto, hhom⟩ := hnil C J n hJ

    have HBq : Scheme.specOver (𝒪 := B') (C ⧸ J) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B')) =
        Scheme.specOver (𝒪 := B) (C ⧸ J) := by
      rw [HB]
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro s hs
      have h1 := congrArg Subtype.val (hinto s hs)
      rw [schemeHomOverComp_coe] at h1
      show schemeHomOverComp _ _ (θ' C s) = E'.L.one _
      apply ext'
      rw [schemeHomOverComp_coe, Category.assoc, θ'g, g_one, C1Aux.one_base_congr E.L HBq]
      exact h1
    ·
      intro s t hs ht hst
      apply hinj s t hs ht
      apply Subtype.ext
      rw [← θ'g, ← θ'g, hst]
    ·
      intro P hP
      let Q : SchemeHomOver (Scheme.specOver (𝒪 := B) C) E.f :=
        ⟨P.1 ≫ g, by rw [Category.assoc, hpb.w, ← Category.assoc, P.2, HB]⟩
      have hQ : E.L.IsInfinitesimal J Q := by
        show schemeHomOverComp _ _ Q = E.L.one _
        apply Subtype.ext
        have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom) ≫ P.1 =
            (E'.L.one (Scheme.specOver (𝒪 := B') (C ⧸ J))).1 := by
          have := congrArg Subtype.val hP
          rw [schemeHomOverComp_coe] at this
          exact this
        rw [schemeHomOverComp_coe, show Q.1 = P.1 ≫ g from rfl, ← Category.assoc, h1, g_one,
          C1Aux.one_base_congr E.L HBq]
      obtain ⟨s, hs, hθs⟩ := honto Q hQ
      refine ⟨s, hs, ?_⟩
      apply ext'
      rw [θ'g, hθs]
    ·
      intro s t hs ht
      have hF : (X.map (algebraMap B B')).F.nilMul n s t = X.F.nilMul n s t := by
        rw [FormalODModule.map_F]; exact C1Aux.nilMul_map (algebraMap B B') rfl X.F n s t
      rw [hF]
      apply ext'
      rw [θ'g, congrArg Subtype.val (hhom s t hs ht), hmul]
      symm
      apply C1Aux.mul_base_congr E.L (HB C)
      · exact θ'g C s
      · exact θ'g C t
  ·
    intro C _ _ J n hJ mm s hs
    letI iC : Algebra B C := ((algebraMap B' C).comp (algebraMap B B')).toAlgebra
    have ha : ∀ i, MvPowerSeries.constantCoeff (X.act (coord mm).1 i) = 0 := (X.isLawHom_act _).1
    have hb : ∀ i, MvPowerSeries.constantCoeff (((X.act (coord mm).2).comp X.varpi) i) = 0 :=
      ((X.isLawHom_act _).comp X.isLawHom_varpi).1
    have hser : Series.addVia (X.map (algebraMap B B')).F ((X.map (algebraMap B B')).act (coord mm).1)
        (((X.map (algebraMap B B')).act (coord mm).2).comp (X.map (algebraMap B B')).varpi) =
        Series.map (algebraMap B B') (Series.addVia X.F (X.act (coord mm).1) ((X.act (coord mm).2).comp X.varpi)) := by
      rw [FormalODModule.map_F, FormalODModule.map_act, FormalODModule.map_act, FormalODModule.map_varpi,
        ← Series.map_comp _ _ _ X.isLawHom_varpi.1, ← Series.map_addVia _ _ _ _ ha hb]
    have htup : (fun i => MvFormalGroup.nilEval n (Series.addVia (X.map (algebraMap B B')).F ((X.map (algebraMap B B')).act (coord mm).1)
        (((X.map (algebraMap B B')).act (coord mm).2).comp (X.map (algebraMap B B')).varpi) i) s) =
        (fun i => MvFormalGroup.nilEval n (Series.addVia X.F (X.act (coord mm).1) ((X.act (coord mm).2).comp X.varpi) i) s) := by
      funext i
      rw [hser]
      exact C1Aux.nilEval_map (algebraMap B B') rfl n _ s
    rw [htup]
    apply ext'
    rw [θ'g, congrArg Subtype.val (hX.2 C J n hJ mm s hs)]
    show (θ C s).1 ≫ E.act mm = ((θ' C s).1 ≫ E'.act mm) ≫ g
    rw [Category.assoc, hact, ← Category.assoc, θ'g]
  ·
    intro B'' _ instB instB' instT s hs
    have hI : instB = ((algebraMap B' B'').comp (algebraMap B B')).toAlgebra :=
      Algebra.algebra_ext _ _ fun r => IsScalarTower.algebraMap_apply B B' B'' r
    subst hI
    exact θ'g B'' s

end S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq (solution)
