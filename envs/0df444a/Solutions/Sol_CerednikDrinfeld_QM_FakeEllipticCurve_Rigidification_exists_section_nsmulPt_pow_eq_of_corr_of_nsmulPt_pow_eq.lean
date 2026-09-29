-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/55923f75-d2f6-531a-a401-1d1480e5cc35

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace N2Level

open CerednikDrinfeld.QM.FakeEllipticCurve

section Square

variable {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}

def img (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem img_coe (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') : (img hg P).1 = P.1 ≫ g := rfl

theorem img_injective (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) {T : Scheme.{0}}
    {t' : T ⟶ Spec (CommRingCat.of S')} {P Q : SchemeHomOver t' f'} (h : img hg P = img hg Q) : P = Q := by
  apply Subtype.ext
  apply hg.hom_ext
  · exact congrArg Subtype.val h
  · rw [P.2, Q.2]

theorem img_one (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    img hg (L'.one t') = L.one (t' ≫ Spec.map (CommRingCat.ofHom φ)) := by
  set x := img hg (L'.one t') with hx
  have hxx : L.mul _ x x = x := by
    apply Subtype.ext
    rw [hx, ← hg_mul, L'.one_mul]
    rfl
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem img_mul (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    img hg (L'.mul t' P Q) = L.mul _ (img hg P) (img hg Q) :=
  Subtype.ext (hg_mul t' P Q)

theorem img_pushPt (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (e : A ⟶ A) (he : e ≫ f = f) (e' : A' ⟶ A') (he' : e' ≫ f' = f') (hcomm : e' ≫ g = g ≫ e)
    {T : Scheme.{0}} {t' : T ⟶ Spec (CommRingCat.of S')} (P : SchemeHomOver t' f') :
    img hg (pushPt e' he' P) = pushPt e he (img hg P) := by
  apply Subtype.ext
  simp only [img_coe, pushPt, mapPt_coe, Category.assoc, hcomm]

theorem img_pow (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g = (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (img hg P) (img hg Q)).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') (n : ℕ) :
    letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ)); letI := L'.pointGroup t'
    img hg (P ^ n) = (img hg P) ^ n := by
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ)); letI := L'.pointGroup t'
  let F : SchemeHomOver t' f' →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
    { toFun := img hg, map_one' := img_one hg L L' hg_mul t', map_mul' := fun X Y => img_mul hg L L' hg_mul t' X Y }
  exact map_pow F P n

end Square

section OneBase

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mapPt_one {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (E.L.one t) = E'.L.one t := by
  set x := mapPt φ hφ (E.L.one t) with hx
  have hxx : E'.L.mul t x x = x := by rw [hx, ← hmul, E.L.one_mul]
  letI := E'.L.pointGroup t
  have h2 : x * x = x * 1 := by rw [mul_one]; exact hxx
  exact mul_left_cancel h2

theorem mapPt_pow {E E' : FakeEllipticCurve Λ N S} (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (n : ℕ) :
    letI := E.L.pointGroup t; letI := E'.L.pointGroup t
    mapPt φ hφ (P ^ n) = (mapPt φ hφ P) ^ n := by
  letI := E.L.pointGroup t; letI := E'.L.pointGroup t
  let F : SchemeHomOver t E.f →* SchemeHomOver t E'.f :=
    { toFun := mapPt φ hφ, map_one' := mapPt_one φ hφ hmul t, map_mul' := fun X Y => hmul t X Y }
  exact map_pow F P n

theorem nsmulPt_eq_pow {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t; nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem pushPt_act_natCast_eq_pow (E : FakeEllipticCurve Λ N S) (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ)
    (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    letI := E.L.pointGroup t; pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩) (E.act_over _) P = P ^ n := by
  rw [CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E h1 n hn t P]
  exact nsmulPt_eq_pow E.L t n P

theorem ft_congr {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (lev : C ⟶ A)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) (Q : SchemeHomOver t' f)
    (h : P.1 = Q.1) : FactorsThrough lev P ↔ FactorsThrough lev Q := by
  unfold FactorsThrough; rw [h]

theorem ft_of_ft_pow {r : ℕ} [Fact r.Prime] (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (K : E.ExtraLevel ℓ) (j : ℕ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (W : SchemeHomOver t E.f)
    (htors : letI := E.L.pointGroup t; W ^ ℓ = 1)
    (hW : letI := E.L.pointGroup t; FactorsThrough K.levK (W ^ (r ^ j))) :
    FactorsThrough K.levK W := by
  classical
  letI := E.L.pointGroup t
  have hℓp : ℓ.Prime := Fact.out
  have hrp : r.Prime := Fact.out
  have hcop : Nat.Coprime (r ^ j) ℓ := Nat.Coprime.pow_left _ ((Nat.coprime_primes hrp hℓp).2 (Ne.symm hℓr))
  have key : ∃ s m : ℕ, s * r ^ j = m * ℓ + 1 := by
    obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓp.one_lt
    refine ⟨s, r ^ j * s / ℓ, ?_⟩
    have := Nat.div_add_mod (r ^ j * s) ℓ
    rw [hs, mul_comm] at this
    rw [mul_comm s]; omega
  obtain ⟨s, m, hsm⟩ := key
  have hnat : ∀ n : ℕ, ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun n => by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul]; push_cast; rw [mul_one]
    rw [this]; exact Λ.smul_mem _ h1
  have hstab := K.levK_stable ⟨((s : ℚ) : ℍ[ℚ, a, b]), hnat s⟩ t _ hW
  rw [pushPt_act_natCast_eq_pow E h1 s (hnat s) t] at hstab
  have : (W ^ r ^ j) ^ s = W := by
    rw [← pow_mul, mul_comm, hsm, pow_add, pow_one, pow_mul', htors, one_pow, one_mul]
  rwa [this] at hstab

end OneBase

section Natural
variable {S : Type} [CommRing S]

theorem act_congr {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N S) {x y : ℍ[ℚ, a, b]}
    (h : x = y) (hx : x ∈ Λ) (hy : y ∈ Λ) : E.act ⟨x, hx⟩ = E.act ⟨y, hy⟩ := by
  subst h; rfl

theorem pow_natural {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (P : SchemeHomOver t f) (k : ℕ) :
    letI := L.pointGroup t; letI := L.pointGroup t'
    schemeHomOverComp ψ hψ (P ^ k) = (schemeHomOverComp ψ hψ P) ^ k := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  let F : SchemeHomOver t f →* SchemeHomOver t' f :=
    { toFun := schemeHomOverComp ψ hψ, map_one' := L.one_natural t t' ψ hψ, map_mul' := fun X Y => L.mul_natural t t' ψ hψ X Y }
  exact map_pow F P k

theorem eq_of_pow_eq_pow_of_coprime {G : Type} [Group G] {a b : G} {M n : ℕ} (hcop : Nat.Coprime M n)
    (ha : a ^ n = 1) (hb : b ^ n = 1) (h : a ^ M = b ^ M) : a = b := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
    have key : ∀ c : G, c ^ n = 1 → (c ^ M) ^ s = c := by
      intro c hc
      have := Nat.div_add_mod (M * s) n
      rw [hs, mul_comm] at this
      rw [← pow_mul, ← this, pow_add, pow_one, pow_mul', hc, one_pow, one_mul]
    rw [← key a ha, ← key b hb, h]
  · interval_cases n
    ·
      have hM : M = 1 := by simpa [Nat.coprime_zero_right] using hcop
      simpa [hM] using h
    · simpa using ha.trans hb.symm

end Natural

theorem corr_exponent
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B}
    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ϱ'.φ' ≫ ϱ'.Eb.act ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ ϱ.φ' ≫ ib ≫ ϱ'.Eb.act ⟨(((r ^ ϱ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by

  set cI : ↥Λ := ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcI
  set cJ : ↥Λ := ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcJ
  set cD : ↥Λ := ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcD
  set cD' : ↥Λ := ⟨(((r ^ ϱ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcD'

  obtain ⟨hφo, hψo, -, -, hlinφ, hlinψ, hcomp⟩ := ϱ.isIsogenyPair
  obtain ⟨hφo', hψo', -, -, hlinφ', hlinψ', hcomp'⟩ := ϱ'.isIsogenyPair
  have hdmem : (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ ϱ.d : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have hdmem' : (((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ ϱ'.d : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have hcD_eq : (⟨(((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hdmem⟩ : ↥Λ) = cD := Subtype.ext (by simp [hcD])
  have hcD'_eq : (⟨(((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hdmem'⟩ : ↥Λ) = cD' := Subtype.ext (by simp [hcD'])
  obtain ⟨h1, h2⟩ := hcomp hdmem
  obtain ⟨h1', h2'⟩ := hcomp' hdmem'
  rw [hcD_eq] at h1 h2
  rw [hcD'_eq] at h1' h2'

  obtain ⟨hsq, -, hlinuA, -⟩ := huA
  have hw : 𝟙 ϱ.Ab.A ≫ ϱ.Ab.f = ϱ.Ab.f ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)) := by simp
  set v : ϱ.Ab.A ⟶ ϱ'.Ab.A := hsq.lift (𝟙 _) ϱ.Ab.f hw with hv
  have hvu : v ≫ uA = 𝟙 _ := hsq.lift_fst _ _ _
  have hvf : v ≫ ϱ'.Ab.f = ϱ.Ab.f := hsq.lift_snd _ _ _
  have huv : uA ≫ v = 𝟙 _ := by
    apply hsq.hom_ext
    · rw [Category.assoc, hvu, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hvf, Category.id_comp]; simpa using hsq.w
  have hlinv : ∀ x : ↥Λ, ϱ.Ab.act x ≫ v = v ≫ ϱ'.Ab.act x := by
    intro x
    calc ϱ.Ab.act x ≫ v = (v ≫ uA) ≫ ϱ.Ab.act x ≫ v := by rw [hvu, Category.id_comp]
      _ = v ≫ (uA ≫ ϱ.Ab.act x) ≫ v := by simp only [Category.assoc]
      _ = v ≫ (ϱ'.Ab.act x ≫ uA) ≫ v := by rw [hlinuA x]
      _ = v ≫ ϱ'.Ab.act x ≫ (uA ≫ v) := by simp only [Category.assoc]
      _ = v ≫ ϱ'.Ab.act x := by rw [huv, Category.comp_id]

  have step1 : ib ≫ ϱ'.Eb.act cD' ≫ ϱ'.Eb.act cI = ϱ.φ ≫ v ≫ ϱ'.φ' ≫ ϱ'.Eb.act cJ := by
    have := congrArg (fun f => f ≫ v ≫ ϱ'.φ') hcorr
    simp only [Category.assoc] at this

    rw [← Category.assoc (ϱ.Ab.act cI) v, hlinv cI, Category.assoc, ← Category.assoc uA v, huv, Category.id_comp,
      hlinψ' cI, ← Category.assoc ϱ'.φ ϱ'.φ', h1', ← Category.assoc (ϱ.Ab.act cJ) v, hlinv cJ, Category.assoc,
      hlinψ' cJ] at this
    exact this

  have step2 := congrArg (fun f => uA ≫ ϱ.φ' ≫ f) step1

  rw [← Category.assoc ϱ.φ' ϱ.φ, h2, ← Category.assoc (ϱ.Ab.act cD) v, hlinv cD, Category.assoc,
    ← Category.assoc uA v, huv, Category.id_comp] at step2
  rw [← Category.assoc (ϱ'.Ab.act cD), hlinψ' cD, Category.assoc] at step2
  exact step2.symm

end N2Level
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq.N2Level"

open N2Level in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    {n : ℕ} (P₀ : A₀.FullLevel n) (hrn : ¬ r ∣ n)
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))

    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (Pn : E.FullLevel n) (Pn' : E'.FullLevel n) (hPn : mapPt i.hom hi Pn.P = Pn'.P)

    (Q : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ϱ.Ab.A) (hQf : Q ≫ ϱ.Ab.f = 𝟙 _)
    (hQg : Q ≫ ϱ.gA = Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) ≫ (P₀.P).1)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hXθ : E.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (hlev : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) ≫ (nsmulPt E.L (𝟙 _) (r ^ t.n) Pn.P).1 =
      Q ≫ ϱ.φ' ≫ ϱ.gb)

    (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B)) (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hκB : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B))
    (hκBψ : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ)
    (hσ : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ϱ.Ab.A,
            PA ≫ ϱ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ϱ.gA = (θ₀ B'' s).1 →
              PA ≫ ϱ.φ' ≫ ϱ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1)
    (htρ : t.ρ = (Series.map κB σ).comp
      ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))))
    :
    ∀ n' : ℕ, n' + (ϱ.d + j₁) = t.n + (ϱ'.d + i₁) →
      ∃ Q' : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ϱ'.Ab.A, Q' ≫ ϱ'.Ab.f = 𝟙 _ ∧
        Q' ≫ ϱ'.gA = Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) ≫ (P₀.P).1 ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) ≫ (nsmulPt E'.L (𝟙 _) (r ^ n') Pn'.P).1 =
          Q' ≫ ϱ'.φ' ≫ ϱ'.gb := by
  classical
  intro n' hn'
  have hrp : r.Prime := Fact.out
  have hsid' : Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnat : ∀ m : ℕ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun m => by
    have := hΛℤ (m : ℤ); rwa [Int.cast_natCast] at this

  have hI := corr_exponent hΛℤ E E' i ϱ ϱ' ib uA huA i₁ j₁ hcorr
  obtain ⟨hsqA, muA, auA, luA⟩ := huA

  have hw : Q ≫ ϱ.Ab.f = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)) := by
    rw [hQf, hsid', Category.comp_id]
  have hQ'u : hsqA.lift Q (𝟙 _) hw ≫ uA = Q := hsqA.lift_fst _ _ _
  have hQ'f : hsqA.lift Q (𝟙 _) hw ≫ ϱ'.Ab.f = 𝟙 _ := hsqA.lift_snd _ _ _
  have hQ'g : hsqA.lift Q (𝟙 _) hw ≫ ϱ'.gA =
      Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) ≫ (P₀.P).1 := by
    rw [← huAg, ← Category.assoc, hQ'u, hQg]
  refine ⟨hsqA.lift Q (𝟙 _) hw, hQ'f, hQ'g, ?_⟩
  set Q' := hsqA.lift Q (𝟙 _) hw with hQ'def

  obtain ⟨hgA, mgA, agA, lgA⟩ := ϱ'.isPullback_Ab
  obtain ⟨hgb, mgb, agb, lgb⟩ := ϱ'.isPullback_Eb
  obtain ⟨hφo, hφ'o, mφ, mφ', aφ, aφ', cφ⟩ := ϱ'.isIsogenyPair

  set s0 : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) :=
    𝟙 _ with hs0
  set mkπ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) with hmk
  set sA := Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) with hsA
  have hb0 : mkπ ≫ 𝟙 (Spec (CommRingCat.of B)) = s0 ≫ mkπ := by rw [hs0, Category.comp_id, Category.id_comp]
  have hb1 : sA ≫ 𝟙 _ = s0 ≫ sA := by rw [hs0, Category.comp_id, Category.id_comp]
  letI iA := ϱ'.Ab.L.pointGroup s0
  letI iEb := ϱ'.Eb.L.pointGroup s0
  letI iE'r := E'.L.pointGroup (s0 ≫ mkπ)
  letI iE' := E'.L.pointGroup (𝟙 (Spec (CommRingCat.of B)))
  letI iE := E.L.pointGroup (𝟙 (Spec (CommRingCat.of B)))
  letI iA₀r := A₀.L.pointGroup (s0 ≫ sA)
  letI iA₀ := A₀.L.pointGroup (𝟙 (Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))))

  set Qp : SchemeHomOver s0 ϱ'.Ab.f := ⟨Q', hQ'f⟩ with hQp
  set Wb : SchemeHomOver s0 ϱ'.Eb.f := mapPt ϱ'.φ' hφ'o Qp with hWb
  set W : SchemeHomOver (s0 ≫ mkπ) E'.f := img hgb Wb with hW
  set P' : SchemeHomOver (s0 ≫ mkπ) E'.f := schemeHomOverComp mkπ hb0 Pn'.P with hP'

  suffices hWV : P' ^ (r ^ n') = W by
    have h2 := congrArg Subtype.val hWV
    rw [hP', ← pow_natural E'.L _ _ mkπ hb0 Pn'.P, ← nsmulPt_eq_pow, schemeHomOverComp_coe] at h2
    rw [h2, hW, hWb, hQp]
    simp only [img_coe, mapPt_coe, Category.assoc]

  have hP't : P' ^ n = 1 := by
    rw [hP', ← pow_natural E'.L _ _ mkπ hb0, ← nsmulPt_eq_pow, Pn'.torsion]
    exact E'.L.one_natural _ _ mkπ hb0

  have himg : img hgA Qp = schemeHomOverComp sA hb1 P₀.P := by
    apply Subtype.ext
    simp only [img_coe, schemeHomOverComp_coe, hQp]
    exact hQ'g
  have hQpt : Qp ^ n = 1 := by
    apply img_injective hgA
    rw [img_pow hgA A₀.L ϱ'.Ab.L mgA, himg, ← pow_natural A₀.L _ _ sA hb1, ← nsmulPt_eq_pow, P₀.torsion,
      A₀.L.one_natural _ _ sA hb1]
    exact (img_one hgA A₀.L ϱ'.Ab.L mgA s0).symm
  have hWbt : Wb ^ n = 1 := by
    rw [hWb, ← mapPt_pow ϱ'.φ' hφ'o mφ' s0 Qp, hQpt]
    exact mapPt_one ϱ'.φ' hφ'o mφ' s0
  have hWt : W ^ n = 1 := by
    rw [hW, ← img_pow hgb E'.L ϱ'.Eb.L mgb, hWbt]
    exact img_one hgb E'.L ϱ'.Eb.L mgb s0

  have hP'pow : ∀ k : ℕ, (P' ^ k).1 = mkπ ≫ (nsmulPt E.L (𝟙 _) k Pn.P).1 ≫ i.hom := by
    intro k
    rw [hP', ← pow_natural E'.L _ _ mkπ hb0 Pn'.P, schemeHomOverComp_coe, ← hPn, ← mapPt_pow i.hom hi hiso.1,
      mapPt_coe, nsmulPt_eq_pow]

  have e1 : ∀ (m : ℕ), ϱ'.Eb.act ⟨(((r ^ m : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ =
      ϱ'.Eb.act ⟨((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ _⟩ :=
    fun m => act_congr ϱ'.Eb (by rw [Int.cast_natCast]) _ _
  have hI' : ϱ'.φ' ≫ ϱ'.Eb.act ⟨(((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ j₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ =
      uA ≫ ϱ.φ' ≫ ib ≫ ϱ'.Eb.act ⟨(((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ i₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
    rw [e1, e1, e1, e1]; exact hI
  have hpowW : W ^ (r ^ ϱ.d * r ^ j₁) = P' ^ (r ^ t.n * (r ^ ϱ'.d * r ^ i₁)) := by
    apply Subtype.ext

    have eL : (W ^ (r ^ ϱ.d * r ^ j₁)).1 = Q' ≫ ϱ'.φ' ≫ ϱ'.gb ≫ E'.act ⟨(((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ ≫
        E'.act ⟨(((r ^ j₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
      rw [pow_mul, ← pushPt_act_natCast_eq_pow E' h1Λ (r ^ ϱ.d) (hnat _) _ W,
        ← pushPt_act_natCast_eq_pow E' h1Λ (r ^ j₁) (hnat _)]
      simp only [pushPt, mapPt_coe, hW, hWb, hQp, img_coe, Category.assoc]

    have eR : (P' ^ (r ^ t.n * (r ^ ϱ'.d * r ^ i₁))).1 = (mkπ ≫ (nsmulPt E.L (𝟙 _) (r ^ t.n) Pn.P).1 ≫ i.hom) ≫
        E'.act ⟨(((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ ≫ E'.act ⟨(((r ^ i₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
      rw [pow_mul, pow_mul, ← pushPt_act_natCast_eq_pow E' h1Λ (r ^ ϱ'.d) (hnat _),
        ← pushPt_act_natCast_eq_pow E' h1Λ (r ^ i₁) (hnat _)]
      simp only [pushPt, mapPt_coe, Category.assoc]
      rw [hP'pow]
      simp only [Category.assoc]
    rw [eL, eR, ← Category.assoc mkπ, hlev]
    have hagb2 : ∀ (x y : ↥Λ), ϱ'.gb ≫ E'.act x ≫ E'.act y = ϱ'.Eb.act x ≫ ϱ'.Eb.act y ≫ ϱ'.gb := by
      intro x y
      rw [← Category.assoc, ← agb, Category.assoc, ← agb]
    rw [hagb2, reassoc_of% hI', ← hagb2, reassoc_of% hibg, reassoc_of% hQ'u]
    simp only [Category.assoc]

  have hexp : r ^ t.n * (r ^ ϱ'.d * r ^ i₁) = r ^ n' * (r ^ ϱ.d * r ^ j₁) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  rw [hexp, pow_mul P' (r ^ n') (r ^ ϱ.d * r ^ j₁)] at hpowW
  have hcop : Nat.Coprime (r ^ ϱ.d * r ^ j₁) n := by
    rw [← pow_add]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hrp).2 hrn)
  have hVt : (P' ^ r ^ n') ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hP't, one_pow]
  exact eq_of_pow_eq_pow_of_coprime hcop hVt hWt hpowW.symm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq (solution)
