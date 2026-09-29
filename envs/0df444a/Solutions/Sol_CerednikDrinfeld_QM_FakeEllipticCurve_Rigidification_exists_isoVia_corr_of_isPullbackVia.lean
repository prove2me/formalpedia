-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fabdfb4d-a8fe-5522-aa13-df2d57571df2

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace P3IsoCorr
universe u
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : GoodReductionJacobian.RelativeGroupLaw R f)
theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]
end P3IsoCorr

open P3IsoCorr in
theorem solution
    {r N : ℕ}
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B B' : Type) [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B)

    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (Eφ : FakeEllipticCurve Λ N B') (g : Eφ.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E Eφ g)
    (E'φ : FakeEllipticCurve Λ N B') (g' : E'φ.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E' E'φ g')
    (ϱφ : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) Eφ) (hϱφ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ϱ ϱφ)
    (ϱ'φ : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E'φ) (hϱ'φ : FakeEllipticCurve.Rigidification.IsPullbackVia φ g' hg' ϱ' ϱ'φ) :
    ∃ (iφ : Eφ.A ≅ E'φ.A) (hiφ : iφ.hom ≫ E'φ.f = Eφ.f) (_ : FakeEllipticCurve.IsoVia Eφ E'φ iφ hiφ)
      (_ : iφ.hom ≫ g' = g ≫ i.hom)
      (ibφ : ϱφ.Eb.A ⟶ ϱ'φ.Eb.A) (_ : ibφ ≫ ϱ'φ.gb = ϱφ.gb ≫ iφ.hom) (_ : ibφ ≫ ϱ'φ.Eb.f = ϱφ.Eb.f)
      (uAφ : ϱ'φ.Ab.A ⟶ ϱφ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱφ.Ab ϱ'φ.Ab uAφ) (_ : uAφ ≫ ϱφ.gA = ϱ'φ.gA),
      ibφ ≫ ϱ'φ.φ ≫ uAφ ≫ ϱφ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱφ.φ ≫ ϱφ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
  obtain ⟨hsqg, gmul, gact, glev⟩ := hg
  obtain ⟨hsqg', g'mul, g'act, g'lev⟩ := hg'
  obtain ⟨hisomul, hisoact, hisolev⟩ := hiso
  obtain ⟨ub, uAϱ, hub, hubg, huAϱ, huAϱg, hd, hφφ⟩ := hϱφ
  obtain ⟨ub', uAϱ', hub', hubg', huAϱ', huAϱ'g, hd', hφφ'⟩ := hϱ'φ
  obtain ⟨huAsq, uAmul, uAact, uAlev⟩ := huA
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have hid' : Spec.map (CommRingCat.ofHom (RingHom.id (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}))) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _

  have ptext : ∀ {S₁ : Type} [CommRing S₁] {X Y Z : Scheme.{0}} {fX : X ⟶ Spec (CommRingCat.of S₁)} {gg : X ⟶ Y} {fY : Y ⟶ Z}
      {s : Spec (CommRingCat.of S₁) ⟶ Z} (hsq : CategoryTheory.IsPullback gg fX fY s)
      {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S₁)} (P Q : SchemeHomOver t fX), P.1 ≫ gg = Q.1 ≫ gg → P = Q := by
    intro S₁ _ X Y Z fX gg fY s hsq T t P Q h
    exact Subtype.ext (hsq.hom_ext h (by rw [P.2, Q.2]))

  have w1 : (g ≫ i.hom) ≫ E'.f = Eφ.f ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B')) := by
    rw [Category.assoc, hi]; exact hsqg.w
  have w2 : (g' ≫ i.inv) ≫ E.f = E'φ.f ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B')) := by
    rw [Category.assoc, ← hi, Iso.inv_hom_id_assoc]; exact hsqg'.w
  let ih : Eφ.A ⟶ E'φ.A := hsqg'.lift (g ≫ i.hom) Eφ.f w1
  let ii : E'φ.A ⟶ Eφ.A := hsqg.lift (g' ≫ i.inv) E'φ.f w2
  have hih₁ : ih ≫ g' = g ≫ i.hom := hsqg'.lift_fst _ _ _
  have hih₂ : ih ≫ E'φ.f = Eφ.f := hsqg'.lift_snd _ _ _
  have hii₁ : ii ≫ g = g' ≫ i.inv := hsqg.lift_fst _ _ _
  have hii₂ : ii ≫ Eφ.f = E'φ.f := hsqg.lift_snd _ _ _
  let iφ : Eφ.A ≅ E'φ.A :=
    { hom := ih, inv := ii,
      hom_inv_id := by
        apply hsqg.hom_ext
        · rw [Category.assoc, hii₁, ← Category.assoc, hih₁, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, hii₂, hih₂, Category.id_comp]
      inv_hom_id := by
        apply hsqg'.hom_ext
        · rw [Category.assoc, hih₁, ← Category.assoc, hii₁, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
        · rw [Category.assoc, hih₂, hii₂, Category.id_comp] }
  have hiφ : iφ.hom ≫ E'φ.f = Eφ.f := hih₂
  have hiφ₁ : iφ.hom ≫ g' = g ≫ i.hom := hih₁
  have hisoφ : FakeEllipticCurve.IsoVia Eφ E'φ iφ hiφ := by
    refine ⟨?_, ?_, ?_⟩
    · intro T t P Q
      apply ptext hsqg'
      rw [mapPt_coe, Category.assoc, hih₁, ← Category.assoc, gmul, g'mul]
      have := congrArg Subtype.val (hisomul (t ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B')))
        ⟨P.1 ≫ g, by rw [Category.assoc, hsqg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hsqg.w, ← Category.assoc, Q.2]⟩)
      rw [mapPt_coe] at this
      rw [this]
      exact mul_val_congr E'.L rfl _ _ _ _ (by simp only [mapPt_coe, Category.assoc, hiφ₁])
        (by simp only [mapPt_coe, Category.assoc, hiφ₁])
    · intro x
      apply hsqg'.hom_ext
      · show (Eφ.act x ≫ ih) ≫ g' = (ih ≫ E'φ.act x) ≫ g'
        rw [Category.assoc, hih₁, ← Category.assoc, gact, Category.assoc, hisoact, Category.assoc, g'act, ← Category.assoc ih g', hih₁,
          Category.assoc]
      · show (Eφ.act x ≫ ih) ≫ E'φ.f = (ih ≫ E'φ.act x) ≫ E'φ.f
        rw [Category.assoc, hih₂, Eφ.act_over, Category.assoc, E'φ.act_over, hih₂]
    · intro T t P
      constructor
      · intro hP
        obtain ⟨P₀, hP₀⟩ := glev t P hP
        have h1 : FactorsThrough E.lev (⟨P.1 ≫ g, by rw [Category.assoc, hsqg.w, ← Category.assoc, P.2]⟩ :
            SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B'))) E.f) := ⟨P₀, hP₀⟩
        obtain ⟨Q₀, hQ₀⟩ := (hisolev _ _).1 h1
        exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback (φ : B →+* B') E' E'φ g' hsqg' g'mul g'lev t (mapPt iφ.hom hiφ P)
          ⟨Q₀, by rw [hQ₀]; simp only [mapPt_coe, Category.assoc, hiφ₁]⟩
      · intro hP
        obtain ⟨P₀, hP₀⟩ := g'lev t _ hP
        have h1 : FactorsThrough E'.lev (mapPt i.hom hi (⟨P.1 ≫ g, by rw [Category.assoc, hsqg.w, ← Category.assoc, P.2]⟩ :
            SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (φ : B →+* B'))) E.f)) :=
          ⟨P₀, by rw [hP₀]; simp only [mapPt_coe, Category.assoc, hiφ₁]⟩
        obtain ⟨Q₀, hQ₀⟩ := (hisolev _ _).2 h1
        exact CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback (φ : B →+* B') E Eφ g hsqg gmul glev t P ⟨Q₀, hQ₀⟩

  have wb : (ub ≫ ib) ≫ ϱ'.Eb.f = ϱφ.Eb.f ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (φ : B →+* B')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from φ.commutes π]
            exact Ideal.subset_span rfl)))))) := by
    rw [Category.assoc, hibf]; exact hub.1.w
  let ibφ : ϱφ.Eb.A ⟶ ϱ'φ.Eb.A := hub'.1.lift (ub ≫ ib) ϱφ.Eb.f wb
  have hibφ₁ : ibφ ≫ ub' = ub ≫ ib := hub'.1.lift_fst _ _ _
  have hibφ₂ : ibφ ≫ ϱ'φ.Eb.f = ϱφ.Eb.f := hub'.1.lift_snd _ _ _
  have hibgφ : ibφ ≫ ϱ'φ.gb = ϱφ.gb ≫ iφ.hom := by
    apply hsqg'.hom_ext
    · show (ibφ ≫ ϱ'φ.gb) ≫ g' = (ϱφ.gb ≫ ih) ≫ g'
      rw [Category.assoc, ← hubg', ← Category.assoc, hibφ₁, Category.assoc, hibg, ← Category.assoc, hubg, Category.assoc, ← hih₁,
        Category.assoc]
    · show (ibφ ≫ ϱ'φ.gb) ≫ E'φ.f = (ϱφ.gb ≫ ih) ≫ E'φ.f
      rw [Category.assoc, ϱ'φ.isPullback_Eb.1.w, ← Category.assoc, hibφ₂, Category.assoc, hih₂, ϱφ.isPullback_Eb.1.w]

  have wA : (uAϱ' ≫ uA) ≫ ϱ.Ab.f = ϱ'φ.Ab.f ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (φ : B →+* B')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from φ.commutes π]
            exact Ideal.subset_span rfl)))))) := by
    rw [Category.assoc, huAsq.w, hid, Category.comp_id]; exact huAϱ'.1.w
  let uAφ : ϱ'φ.Ab.A ⟶ ϱφ.Ab.A := huAϱ.1.lift (uAϱ' ≫ uA) ϱ'φ.Ab.f wA
  have huAφ₁ : uAφ ≫ uAϱ = uAϱ' ≫ uA := huAϱ.1.lift_fst _ _ _
  have huAφ₂ : uAφ ≫ ϱφ.Ab.f = ϱ'φ.Ab.f := huAϱ.1.lift_snd _ _ _
  obtain ⟨huAϱsq, uAϱmul, uAϱact, uAϱlev⟩ := huAϱ
  obtain ⟨huAϱ'sq, uAϱ'mul, uAϱ'act, uAϱ'lev⟩ := huAϱ'
  have hsqφ : CategoryTheory.IsPullback uAφ ϱ'φ.Ab.f ϱφ.Ab.f (Spec.map (CommRingCat.ofHom (RingHom.id (B' ⧸ Ideal.span {algebraMap 𝒪 B' π})))) := by
    have big : CategoryTheory.IsPullback (uAϱ' ≫ uA) ϱ'φ.Ab.f ϱ.Ab.f
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (φ : B →+* B')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from φ.commutes π]
            exact Ideal.subset_span rfl)))))) ≫ Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π})))) := huAϱ'sq.paste_horiz huAsq
    rw [hid, Category.comp_id] at big
    have s : CategoryTheory.IsPullback (uAφ ≫ uAϱ) ϱ'φ.Ab.f ϱ.Ab.f
        (Spec.map (CommRingCat.ofHom (RingHom.id (B' ⧸ Ideal.span {algebraMap 𝒪 B' π}))) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (φ : B →+* B')
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (φ : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from φ.commutes π]
            exact Ideal.subset_span rfl))))))) := by
      rw [huAφ₁, hid', Category.id_comp]; exact big
    exact s.of_right (by rw [huAφ₂, hid', Category.comp_id]) huAϱsq
  have huAφ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱφ.Ab ϱ'φ.Ab uAφ := by
    refine ⟨hsqφ, ?_, ?_, ?_⟩
    · intro T t P Q
      apply huAϱsq.hom_ext
      · rw [Category.assoc, huAφ₁, ← Category.assoc, uAϱ'mul, uAmul, uAϱmul]
        exact mul_val_congr ϱ.Ab.L (by simp only [hid, hid', Category.comp_id, Category.id_comp, Category.assoc]) _ _ _ _
          (by simp only [Category.assoc, huAφ₁]) (by simp only [Category.assoc, huAφ₁])
      · rw [Category.assoc, huAφ₂, (ϱ'φ.Ab.L.mul t P Q).2, (ϱφ.Ab.L.mul _ _ _).2, hid', Category.comp_id]
    · intro x
      apply huAϱsq.hom_ext
      · rw [Category.assoc, huAφ₁, ← Category.assoc, uAϱ'act, Category.assoc, uAact, Category.assoc, uAϱact, ← Category.assoc uAφ, huAφ₁,
          Category.assoc]
      · rw [Category.assoc, huAφ₂, ϱ'φ.Ab.act_over, Category.assoc, ϱφ.Ab.act_over, huAφ₂]
    · intro T t P hP
      obtain ⟨P₀, hP₀⟩ := uAϱ'lev t P hP
      obtain ⟨P₁, hP₁⟩ := uAlev _ ⟨P.1 ≫ uAϱ', by rw [Category.assoc, huAϱ'sq.w, ← Category.assoc, P.2]⟩ ⟨P₀, hP₀⟩
      have h2 := CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback _ ϱ.Ab ϱφ.Ab uAϱ huAϱsq uAϱmul uAϱlev
        (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id _))) ⟨P.1 ≫ uAφ, by rw [Category.assoc, huAφ₂, P.2, hid', Category.comp_id]⟩
        ⟨P₁, by rw [hP₁]; simp only [Category.assoc, huAφ₁]⟩
      exact h2
  have huAgφ : uAφ ≫ ϱφ.gA = ϱ'φ.gA := by
    rw [← huAϱg, ← Category.assoc, huAφ₁, Category.assoc, huAg, huAϱ'g]

  have hcorrφ : ibφ ≫ ϱ'φ.φ ≫ uAφ ≫ ϱφ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱφ.φ ≫ ϱφ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    apply huAϱsq.hom_ext
    · simp only [Category.assoc]
      rw [uAϱact, uAϱact, ← Category.assoc uAφ uAϱ, huAφ₁]
      simp only [Category.assoc]
      rw [← Category.assoc ϱ'φ.φ uAϱ', ← hφφ']
      simp only [Category.assoc]
      rw [← Category.assoc ibφ ub', hibφ₁]
      simp only [Category.assoc]
      rw [hcorr, ← Category.assoc ϱφ.φ uAϱ, ← hφφ, Category.assoc]
    · simp only [Category.assoc, ϱφ.Ab.act_over, huAφ₂, ϱ'φ.φ_over, hibφ₂, ϱφ.φ_over]
  exact ⟨iφ, hiφ, hisoφ, hih₁, ibφ, hibgφ, hibφ₂, uAφ, huAφ, huAgφ, hcorrφ⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia (solution)
