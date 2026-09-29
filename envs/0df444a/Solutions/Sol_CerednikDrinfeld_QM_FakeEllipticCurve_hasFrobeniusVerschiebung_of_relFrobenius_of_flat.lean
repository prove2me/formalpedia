-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_relFrobenius_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b2c79c60-833a-5b17-984e-b1bfca756c57

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_relFrobenius_of_flat
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace GC3bC0
open GoodReductionJacobian

variable {R : Type u} [CommRing R]

theorem nsmulPt_natural {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
    show schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n x) x) = L.mul t' (nsmulPt L t' n _) _
    rw [L.mul_natural, ih]

theorem nsmulPt_coe {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (nsmulPt L t n x).1 = x.1 ≫ (nsmulPt L f n ⟨𝟙 A, Category.id_comp f⟩).1 := by
  have h := nsmulPt_natural L f t x.1 x.2 n ⟨𝟙 A, Category.id_comp f⟩
  have hx : schemeHomOverComp x.1 x.2 (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem mapPt_one {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h : mapPt φ hφ (L.one t) * mapPt φ hφ (L.one t) = mapPt φ hφ (L.one t) := by
    show L'.mul t _ _ = _
    rw [← hom, L.one_mul]
  exact mul_eq_right.mp h

theorem mapPt_nsmulPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hom t
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n _) _
    rw [hom, ih]

theorem pushPt_nsmulPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    pushPt φ hφ (nsmulPt L t n P) = nsmulPt L t n (pushPt φ hφ P) :=
  mapPt_nsmulPt L L φ hφ hom t n P

theorem factorsThrough_nsmulPt {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (lev : C ⟶ A)
    (lev_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q → FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    (lev_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f)
    (hP : FactorsThrough lev P) : FactorsThrough lev (nsmulPt L t n P) := by
  induction n with
  | zero => exact lev_one t
  | succ n ih => exact (lev_sub t _ _ ih hP).1

theorem nsmulPt_mul_of_isCommutative {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P Q : SchemeHomOver t f) :
    nsmulPt L t n (L.mul t P Q) = L.mul t (nsmulPt L t n P) (nsmulPt L t n Q) := by
  letI := L.pointGroup t
  have hp : ∀ (x : SchemeHomOver t f) (n : ℕ), nsmulPt L t n x = x ^ n := by
    intro x n
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih =>
      show L.mul t (nsmulPt L t n x) x = x ^ (n + 1)
      rw [pow_succ, ih]; rfl
  rw [hp, hp, hp]
  show (P * Q) ^ n = P ^ n * Q ^ n
  exact (show Commute P Q from hc t P Q).mul_pow n

end GC3bC0

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP k ℓ]
    (E Eℓ : FakeEllipticCurve Λ N k)
    (pr : Eℓ.A ⟶ E.A)
    (pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius k ℓ))))
    (pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t' Eℓ.f),
      (Eℓ.L.mul t' P Q).1 ≫ pr =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius k ℓ)))
          ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1)
    (pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x)
    (pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr)
    (pr_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t' Eℓ.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr) → FactorsThrough Eℓ.lev P)
    (hA : (ℓ : Γ(E.A, ⊤)) = 0)
    (F : E.A ⟶ Eℓ.A) (F_over : F ≫ Eℓ.f = E.f) (F_pr : F ≫ pr = E.A.frobenius ℓ 1 hℓ.out hA)
    (F_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q))
    (F_act : ∀ x : ↥Λ, E.act x ≫ F = F ≫ Eℓ.act x)
    (F_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough Eℓ.lev (mapPt F F_over P))
    [IsAlgClosed k] (hℓN : ¬ ℓ ∣ N) [Flat F] [Surjective F] [IsFinite F] :
    HasFrobeniusVerschiebung ℓ E Eℓ := by
  classical
  have hk0 : (ℓ : k) = 0 := CharP.cast_eq_zero k ℓ
  have hS : (ℓ : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec hk0

  let idE : SchemeHomOver E.f E.f := ⟨𝟙 E.A, Category.id_comp _⟩
  let idℓ : SchemeHomOver Eℓ.f Eℓ.f := ⟨𝟙 Eℓ.A, Category.id_comp _⟩
  let m : E.A ⟶ E.A := (nsmulPt E.L E.f ℓ idE).1
  let mℓ : Eℓ.A ⟶ Eℓ.A := (nsmulPt Eℓ.L Eℓ.f ℓ idℓ).1
  have hm_over : m ≫ E.f = E.f := (nsmulPt E.L E.f ℓ idE).2
  have hnsE : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      (nsmulPt E.L t ℓ P).1 = P.1 ≫ m := fun t P => GC3bC0.nsmulPt_coe E.L t ℓ P
  have hnsℓ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eℓ.f),
      (nsmulPt Eℓ.L t ℓ Q).1 = Q.1 ≫ mℓ := fun t Q => GC3bC0.nsmulPt_coe Eℓ.L t ℓ Q

  have hcoeq : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ E.A), g₁ ≫ F = g₂ ≫ F → g₁ ≫ m = g₂ ≫ m := by
    intro Z g₁ g₂ h
    have ht : g₂ ≫ E.f = g₁ ≫ E.f := by rw [← F_over, ← Category.assoc, ← h, Category.assoc]
    have key := nsmulPt_eq_of_mapPt_relFrobenius_eq k ℓ E Eℓ pr pr_isPullback pr_mul pr_act pr_lev pr_lev' hA F F_over
      F_pr F_hom (g₁ ≫ E.f) ⟨g₁, rfl⟩ ⟨g₂, ht⟩ (Subtype.ext h)
    have h2 := congrArg Subtype.val key
    rwa [hnsE, hnsE] at h2

  haveI : EffectiveEpi F := inferInstance
  haveI : Epi F := inferInstance
  let V : Eℓ.A ⟶ E.A := EffectiveEpi.desc F m hcoeq
  have hFV : F ≫ V = m := EffectiveEpi.fac F m hcoeq
  have V_over : V ≫ E.f = Eℓ.f := by
    rw [← cancel_epi F, ← Category.assoc, hFV, hm_over, F_over]

  have hFm : m ≫ F = F ≫ mℓ := by
    have h1 := congrArg Subtype.val (GC3bC0.mapPt_nsmulPt E.L Eℓ.L F F_over F_hom E.f ℓ idE)
    rw [hnsℓ] at h1
    change m ≫ F = (𝟙 E.A ≫ F) ≫ mℓ at h1
    rwa [Category.id_comp] at h1
  have hVF : V ≫ F = mℓ := by rw [← cancel_epi F, ← Category.assoc, hFV, hFm]

  have V_F : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      mapPt V V_over (mapPt F F_over P) = nsmulPt E.L t ℓ P := by
    intro T t P
    apply Subtype.ext
    rw [hnsE]
    show (P.1 ≫ F) ≫ V = P.1 ≫ m
    rw [Category.assoc, hFV]
  have F_V : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eℓ.f),
      mapPt F F_over (mapPt V V_over Q) = nsmulPt Eℓ.L t ℓ Q := by
    intro T t Q
    apply Subtype.ext
    rw [hnsℓ]
    show (Q.1 ≫ V) ≫ F = Q.1 ≫ mℓ
    rw [Category.assoc, hVF]

  have V_act : ∀ x : ↥Λ, Eℓ.act x ≫ V = V ≫ E.act x := by
    intro x
    have hmx : m ≫ E.act x = E.act x ≫ m := by
      have h1 := congrArg Subtype.val (GC3bC0.pushPt_nsmulPt E.L (E.act x) (E.act_over x) (E.act_hom x) E.f ℓ idE)
      rw [hnsE] at h1
      change m ≫ E.act x = (𝟙 E.A ≫ E.act x) ≫ m at h1
      rwa [Category.id_comp] at h1
    rw [← cancel_epi F, ← Category.assoc, ← F_act, Category.assoc, hFV, ← Category.assoc, hFV, hmx]

  have V_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t Eℓ.f),
      FactorsThrough Eℓ.lev Q → FactorsThrough E.lev (mapPt V V_over Q) := by
    intro T t Q hQ
    obtain ⟨P, ⟨hPlev, hPQ⟩, -⟩ := existsUnique_factorsThrough_mapPt_relFrobenius_eq_of_not_dvd_of_isAlgClosed k ℓ E Eℓ pr pr_isPullback
      pr_mul pr_act pr_lev pr_lev' hA F F_over F_pr F_hom hℓN t Q hQ
    rw [← hPQ, V_F]
    exact GC3bC0.factorsThrough_nsmulPt E.L E.lev E.lev_sub E.lev_one t ℓ P hPlev

  have hpow : ∀ (B : Type u) [CommRing B] [CharP B ℓ],
      powCharRingHom B ℓ 1 hℓ.out (CharP.cast_eq_zero B ℓ) = frobenius B ℓ := by
    intro B _ _; ext x; simp [frobenius, powCharRingHom_apply]
  have F_frob : ∀ (B : Type u) [CommRing B] [CharP B ℓ] (x : Spec (CommRingCat.of B) ⟶ E.A),
      x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B ℓ)) ≫ x := by
    intro B _ _ x
    have hB : (ℓ : Γ(Spec (CommRingCat.of B), ⊤)) = 0 := Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero B ℓ)
    rw [F_pr, ← hpow B, ← Scheme.frobenius_Spec ℓ 1 hℓ.out (CharP.cast_eq_zero B ℓ)]
    exact (Scheme.frobenius_comp x ℓ 1 hℓ.out hB hA).symm

  have V_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t Eℓ.f),
      mapPt V V_over (Eℓ.L.mul t P Q) = E.L.mul t (mapPt V V_over P) (mapPt V V_over Q) := by
    intro T t P Q

    let p₁ := pullback.fst Eℓ.f Eℓ.f
    let p₂ := pullback.snd Eℓ.f Eℓ.f
    let tY : pullback Eℓ.f Eℓ.f ⟶ Spec (CommRingCat.of k) := p₁ ≫ Eℓ.f
    let U₁ : SchemeHomOver tY Eℓ.f := ⟨p₁, rfl⟩
    let U₂ : SchemeHomOver tY Eℓ.f := ⟨p₂, pullback.condition.symm⟩

    have key : (Eℓ.L.mul tY U₁ U₂).1 ≫ V = (E.L.mul tY (mapPt V V_over U₁) (mapPt V V_over U₂)).1 := by
      let q₁ := pullback.fst E.f E.f
      let q₂ := pullback.snd E.f E.f
      let tX : pullback E.f E.f ⟶ Spec (CommRingCat.of k) := q₁ ≫ E.f
      have e₁ : E.f = F ≫ Eℓ.f := F_over.symm
      let G : pullback E.f E.f ⟶ pullback Eℓ.f Eℓ.f :=
        pullback.map E.f E.f Eℓ.f Eℓ.f F F (𝟙 _) (by rw [Category.comp_id, e₁]) (by rw [Category.comp_id, e₁])
      have hG₁ : G ≫ p₁ = q₁ ≫ F := pullback.lift_fst _ _ _
      have hG₂ : G ≫ p₂ = q₂ ≫ F := pullback.lift_snd _ _ _
      have hGt : G ≫ tY = tX := by
        show G ≫ p₁ ≫ Eℓ.f = q₁ ≫ E.f
        rw [← Category.assoc, hG₁, Category.assoc, F_over]
      have hGflat : Flat G := MorphismProperty.pullbackMap (P := @Flat) ‹Flat F› ‹Flat F› e₁ e₁
      have hGsurj : Surjective G := MorphismProperty.pullbackMap (P := @Surjective) ‹Surjective F› ‹Surjective F› e₁ e₁
      have hGqc : QuasiCompact G :=
        MorphismProperty.pullbackMap (P := @QuasiCompact) (inferInstance : QuasiCompact F) (inferInstance : QuasiCompact F) e₁ e₁
      haveI : Epi G := by haveI := hGflat; haveI := hGsurj; haveI := hGqc; infer_instance
      let Q₁ : SchemeHomOver tX E.f := ⟨q₁, rfl⟩
      let Q₂ : SchemeHomOver tX E.f := ⟨q₂, pullback.condition.symm⟩
      have hc1 : GoodReductionJacobian.schemeHomOverComp G hGt U₁ = mapPt F F_over Q₁ := Subtype.ext hG₁
      have hc2 : GoodReductionJacobian.schemeHomOverComp G hGt U₂ = mapPt F F_over Q₂ := Subtype.ext hG₂
      have hd1 : GoodReductionJacobian.schemeHomOverComp G hGt (mapPt V V_over U₁) = nsmulPt E.L tX ℓ Q₁ := Subtype.ext (by
        rw [hnsE]
        show G ≫ p₁ ≫ V = q₁ ≫ m
        rw [← Category.assoc, hG₁, Category.assoc, hFV])
      have hd2 : GoodReductionJacobian.schemeHomOverComp G hGt (mapPt V V_over U₂) = nsmulPt E.L tX ℓ Q₂ := Subtype.ext (by
        rw [hnsE]
        show G ≫ p₂ ≫ V = q₂ ≫ m
        rw [← Category.assoc, hG₂, Category.assoc, hFV])
      rw [← cancel_epi G]
      have lhs : G ≫ (Eℓ.L.mul tY U₁ U₂).1 ≫ V = (nsmulPt E.L tX ℓ (E.L.mul tX Q₁ Q₂)).1 := by
        rw [← Category.assoc]
        change (GoodReductionJacobian.schemeHomOverComp G hGt (Eℓ.L.mul tY U₁ U₂)).1 ≫ V = _
        rw [Eℓ.L.mul_natural, hc1, hc2, ← F_hom, hnsE]
        show ((E.L.mul tX Q₁ Q₂).1 ≫ F) ≫ V = _
        rw [Category.assoc, hFV]
      have rhs : G ≫ (E.L.mul tY (mapPt V V_over U₁) (mapPt V V_over U₂)).1 =
          (E.L.mul tX (nsmulPt E.L tX ℓ Q₁) (nsmulPt E.L tX ℓ Q₂)).1 := by
        change (GoodReductionJacobian.schemeHomOverComp G hGt (E.L.mul tY (mapPt V V_over U₁) (mapPt V V_over U₂))).1 = _
        rw [E.L.mul_natural, hd1, hd2]
      rw [lhs, rhs, GC3bC0.nsmulPt_mul_of_isCommutative E.L E.comm]

    let ψ : T ⟶ pullback Eℓ.f Eℓ.f := pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)
    have hψ : ψ ≫ tY = t := by
      show ψ ≫ p₁ ≫ Eℓ.f = t
      rw [← Category.assoc, pullback.lift_fst, P.2]
    have hP : GoodReductionJacobian.schemeHomOverComp ψ hψ U₁ = P := Subtype.ext (pullback.lift_fst _ _ _)
    have hQ : GoodReductionJacobian.schemeHomOverComp ψ hψ U₂ = Q := Subtype.ext (pullback.lift_snd _ _ _)
    have h1 : mapPt V V_over (GoodReductionJacobian.schemeHomOverComp ψ hψ U₁) = GoodReductionJacobian.schemeHomOverComp ψ hψ (mapPt V V_over U₁) :=
      Subtype.ext (Category.assoc _ _ _)
    have h2 : mapPt V V_over (GoodReductionJacobian.schemeHomOverComp ψ hψ U₂) = GoodReductionJacobian.schemeHomOverComp ψ hψ (mapPt V V_over U₂) :=
      Subtype.ext (Category.assoc _ _ _)
    rw [← hP, ← hQ, ← Eℓ.L.mul_natural tY t ψ hψ U₁ U₂, h1, h2, ← E.L.mul_natural tY t ψ hψ]
    apply Subtype.ext
    show (ψ ≫ (Eℓ.L.mul tY U₁ U₂).1) ≫ V = ψ ≫ (E.L.mul tY (mapPt V V_over U₁) (mapPt V V_over U₂)).1
    rw [Category.assoc, key]
  exact ⟨⟨pr, pr_isPullback, pr_mul, pr_act, pr_lev, F, F_over, V, V_over, F_hom, V_hom, F_act, V_act, F_lev, V_lev,
    V_F, F_V, F_frob⟩⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_relFrobenius_of_flat
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_relFrobenius_of_flat (solution)
