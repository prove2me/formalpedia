-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/eecec370-c79a-5bd2-ac43-0c1c59236f2e

import Mathlib.Data.Int.GCD
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace P3LevelTransport

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve GoodReductionJacobian

section Points

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

theorem mapPt_mapPt (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) h P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.assoc]

theorem mapPt_congr {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

theorem mapPt_id (h : 𝟙 A ≫ f = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (𝟙 A) h P = P := by
  apply Subtype.ext
  simp only [mapPt_coe, Category.comp_id]

variable (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem eq_one_of_mul_self_eq {x : SchemeHomOver t f} (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem hom_one (F : SchemeHomOver t f → SchemeHomOver t f')
    (hF : ∀ P Q : SchemeHomOver t f, F (L.mul t P Q) = L'.mul t (F P) (F Q)) :
    F (L.one t) = L'.one t := by
  apply eq_one_of_mul_self_eq L' t
  rw [← hF, L.one_mul]

theorem nsmulPt_zero (P : SchemeHomOver t f) : nsmulPt L t 0 P = L.one t := rfl

theorem nsmulPt_succ (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t (n + 1) P = L.mul t (nsmulPt L t n P) P := rfl

theorem hom_nsmulPt (F : SchemeHomOver t f → SchemeHomOver t f')
    (hF : ∀ P Q : SchemeHomOver t f, F (L.mul t P Q) = L'.mul t (F P) (F Q)) (n : ℕ) (P : SchemeHomOver t f) :
    F (nsmulPt L t n P) = nsmulPt L' t n (F P) := by
  induction n with
  | zero => exact hom_one L L' t F hF
  | succ n ih => rw [nsmulPt_succ, nsmulPt_succ, hF, ih]

theorem nsmulPt_one (n : ℕ) : nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmulPt_succ, ih, L.one_mul]

theorem nsmulPt_add (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (m + n) P = L.mul t (nsmulPt L t m P) (nsmulPt L t n P) := by
  induction n with
  | zero => rw [Nat.add_zero, nsmulPt_zero, L.mul_one]
  | succ n ih => rw [← Nat.add_assoc, nsmulPt_succ, nsmulPt_succ, ih, L.mul_assoc]

theorem nsmulPt_mul (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (m * n) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => rw [Nat.mul_zero, nsmulPt_zero, nsmulPt_zero]
  | succ n ih => rw [Nat.mul_succ, nsmulPt_add, ih, nsmulPt_succ]

end Points

section Act

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
  (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem act_zero (P : SchemeHomOver t E.f) : pushPt (E.act 0) (E.act_over 0) P = E.L.one t := by
  have h := E.act_add 0 0 t P
  rw [add_zero] at h
  exact eq_one_of_mul_self_eq E.L t h.symm

theorem act_nsmul (n : ℕ) (x : ↥Λ) (P : SchemeHomOver t E.f) :
    pushPt (E.act (n • x)) (E.act_over (n • x)) P = nsmulPt E.L t n (pushPt (E.act x) (E.act_over x) P) := by
  induction n with
  | zero => rw [zero_nsmul, nsmulPt_zero]; exact act_zero E t P
  | succ n ih => rw [succ_nsmul, E.act_add, ih, nsmulPt_succ]

theorem act_natCast (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩) (E.act_over _) P = nsmulPt E.L t n P := by
  have he : (⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ : ↥Λ) = n • (⟨1, h1⟩ : ↥Λ) := by
    apply Subtype.ext
    simp [nsmul_eq_mul, QuaternionAlgebra.coe_natCast]
  rw [he, act_nsmul]
  congr 1
  exact (mapPt_congr (E.act_one h1) _ (by rw [Category.id_comp]) P).trans (mapPt_id _ P)

end Act

section MoreGroup

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

theorem mul_inv_cancel (x : SchemeHomOver t f) : L.mul t x (L.inv t x) = L.one t := by
  apply eq_one_of_mul_self_eq L t
  calc L.mul t (L.mul t x (L.inv t x)) (L.mul t x (L.inv t x))
      = L.mul t x (L.mul t (L.inv t x) (L.mul t x (L.inv t x))) := L.mul_assoc t _ _ _
    _ = L.mul t x (L.mul t (L.mul t (L.inv t x) x) (L.inv t x)) := by rw [L.mul_assoc]
    _ = L.mul t x (L.inv t x) := by rw [L.inv_mul_cancel, L.one_mul]

theorem inv_eq_of_mul_eq_one {x y : SchemeHomOver t f} (h : L.mul t y x = L.one t) : L.inv t x = y := by
  calc L.inv t x = L.mul t (L.one t) (L.inv t x) := (L.one_mul t _).symm
    _ = L.mul t (L.mul t y x) (L.inv t x) := by rw [h]
    _ = L.mul t y (L.mul t x (L.inv t x)) := L.mul_assoc t _ _ _
    _ = y := by rw [mul_inv_cancel, L.mul_one]

theorem hom_inv (F : SchemeHomOver t f → SchemeHomOver t f')
    (hF : ∀ P Q : SchemeHomOver t f, F (L.mul t P Q) = L'.mul t (F P) (F Q)) (P : SchemeHomOver t f) :
    F (L.inv t P) = L'.inv t (F P) := by
  symm
  apply inv_eq_of_mul_eq_one L' t
  rw [← hF, L.inv_mul_cancel, hom_one L L' t F hF]

end MoreGroup

end P3LevelTransport

open P3LevelTransport GoodReductionJacobian CerednikDrinfeld.QM.FakeEllipticCurve in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {N : ℕ}
    {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (r d : ℕ) [Fact r.Prime] (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
    (hiso : FakeEllipticCurve.IsIsogenyPair (r ^ d) E E' φ ψ) (hlev : FakeEllipticCurve.PreservesLevel E E' φ hφ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓ : IsUnit ((ℓ : ℕ) : S))
    (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K.levK P → FactorsThrough K'.levK (mapPt φ hφ P)) ∧
      ∀ K₂ : E.ExtraLevel ℓ,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
            FactorsThrough K₂.levK P → FactorsThrough K'.levK (mapPt φ hφ P)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K.levK P ↔ FactorsThrough K₂.levK P := by
  classical
  obtain ⟨hφ₀, hψ, hmulφ, hmulψ, hlinφ, hlinψ, hdeg⟩ := hiso
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ (r ^ d : ℕ)
  obtain ⟨hφψ, hψφ⟩ := hdeg hd
  have hmulφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q) := hmulφ

  obtain ⟨c, e, hbez⟩ : ∃ c e : ℕ, c * r ^ d = ℓ * e + 1 := by
    have hr : r.Prime := Fact.out
    have hl : ℓ.Prime := Fact.out
    have hcop : Nat.Coprime (r ^ d) ℓ :=
      Nat.Coprime.pow_left d ((Nat.coprime_primes hr hl).mpr (Ne.symm hℓr))
    obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hl.one_lt
    exact ⟨c, r ^ d * c / ℓ, by have := Nat.div_add_mod (r ^ d * c) ℓ; rw [hc] at this; rw [Nat.mul_comm c]; omega⟩
  have hc : (((c : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ (c : ℕ)

  have hψφ_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt E'.L t (r ^ d) Q := by
    intro T t Q
    rw [mapPt_mapPt ψ hψ φ hφ (by rw [Category.assoc, hφ, hψ]), mapPt_congr hψφ _ (E'.act_over _)]
    exact act_natCast E' t h1 _ hd Q
  have hφψ_pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f),
      mapPt ψ hψ (mapPt φ hφ Q) = nsmulPt E.L t (r ^ d) Q := by
    intro T t Q
    rw [mapPt_mapPt φ hφ ψ hψ (by rw [Category.assoc, hψ, hφ]), mapPt_congr hφψ _ (E.act_over _)]
    exact act_natCast E t h1 _ hd Q
  have hlinφ_pt : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f),
      mapPt φ hφ (pushPt (E.act x) (E.act_over x) Q) = pushPt (E'.act x) (E'.act_over x) (mapPt φ hφ Q) := by
    intro x T t Q
    delta pushPt
    rw [mapPt_mapPt _ _ _ _ (by rw [Category.assoc, hφ, E.act_over]),
      mapPt_mapPt _ _ _ _ (by rw [Category.assoc, E'.act_over, hφ])]
    exact mapPt_congr (hlinφ x) _ _ Q
  have hlinψ_pt : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (pushPt (E'.act x) (E'.act_over x) Q) = pushPt (E.act x) (E.act_over x) (mapPt ψ hψ Q) := by
    intro x T t Q
    delta pushPt
    rw [mapPt_mapPt _ _ _ _ (by rw [Category.assoc, hψ, E'.act_over]),
      mapPt_mapPt _ _ _ _ (by rw [Category.assoc, E.act_over, hψ])]
    exact mapPt_congr (hlinψ x) _ _ Q

  have hcrd : ∀ {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
      {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f),
      nsmulPt L t ℓ Q = L.one t → nsmulPt L t c (nsmulPt L t (r ^ d) Q) = Q := by
    intro A f L T t Q hQ
    rw [← nsmulPt_mul, Nat.mul_comm, hbez, nsmulPt_succ, nsmulPt_mul, hQ, nsmulPt_one, L.one_mul]

  obtain ⟨ψ', hψ'def⟩ : ∃ ψ' : E'.A ⟶ E.A, ψ' = ψ ≫ E.act ⟨_, hc⟩ := ⟨_, rfl⟩
  have hψ' : ψ' ≫ E.f = E'.f := by rw [hψ'def, Category.assoc, E.act_over, hψ]
  have hψ'pt : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.f),
      mapPt ψ' hψ' Q = pushPt (E.act ⟨_, hc⟩) (E.act_over _) (mapPt ψ hψ Q) := by
    intro T t Q; subst hψ'def; exact (mapPt_mapPt _ _ _ _ _ Q).symm
  have hmulψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ' hψ' (E'.L.mul t P Q) = E.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q) := by
    intro T t P Q; rw [hψ'pt, hψ'pt, hψ'pt, hmulψ, E.act_hom]
  have hlinψ'_pt : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.f),
      mapPt ψ' hψ' (pushPt (E'.act x) (E'.act_over x) Q) = pushPt (E.act x) (E.act_over x) (mapPt ψ' hψ' Q) := by
    intro x T t Q
    rw [hψ'pt, hψ'pt, hlinψ_pt]
    have hcx : (((c : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [QuaternionAlgebra.coe_mul_eq_smul, Nat.cast_smul_eq_nsmul]; exact nsmul_mem x.2 _
    have hxc : (x : ℍ[ℚ, a, b]) * (((c : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
      rw [← QuaternionAlgebra.coe_commutes]; exact hcx
    have hel : (⟨_, hcx⟩ : ↥Λ) = ⟨_, hxc⟩ := Subtype.ext (QuaternionAlgebra.coe_commutes _ _)
    delta pushPt
    rw [mapPt_mapPt (E.act x) (E.act_over x) (E.act ⟨_, hc⟩) (E.act_over _)
        (by rw [Category.assoc, E.act_over, E.act_over]),
      mapPt_mapPt (E.act ⟨_, hc⟩) (E.act_over _) (E.act x) (E.act_over x)
        (by rw [Category.assoc, E.act_over, E.act_over]),
      ← mapPt_congr (E.act_mul ⟨_, hc⟩ x hcx) (E.act_over _), ← mapPt_congr (E.act_mul x ⟨_, hc⟩ hxc) (E.act_over _)]
    exact mapPt_congr (congrArg E.act hel) _ _ _

  have hF1 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E'.f),
      nsmulPt E'.L t ℓ Q = E'.L.one t → mapPt φ hφ (mapPt ψ' hψ' Q) = Q := by
    intro T t Q hQ
    rw [hψ'pt, hlinφ_pt, hψφ_pt]
    rw [show pushPt (E'.act ⟨_, hc⟩) (E'.act_over _) (nsmulPt E'.L t (r ^ d) Q) = _ from act_natCast E' t h1 c hc _]
    exact hcrd E'.L t Q hQ
  have hF2 : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      nsmulPt E.L t ℓ P = E.L.one t → mapPt ψ' hψ' (mapPt φ hφ P) = P := by
    intro T t P hP
    rw [hψ'pt, hφψ_pt]
    rw [show pushPt (E.act ⟨_, hc⟩) (E.act_over _) (nsmulPt E.L t (r ^ d) P) = _ from act_natCast E t h1 c hc _]
    exact hcrd E.L t P hP

  have hunivK' : K'.levK ≫ ψ' ≫ φ = K'.levK := by
    have htor := K'.levK_torsion (K'.levK ≫ E'.f) ⟨K'.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
    have := congrArg Subtype.val (hF1 _ _ htor)
    simpa only [mapPt_coe, Category.assoc] using this

  have char : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough (K'.levK ≫ ψ') P ↔ ∃ Q : SchemeHomOver t E'.f, FactorsThrough K'.levK Q ∧ mapPt ψ' hψ' Q = P := by
    intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨⟨P₀ ≫ K'.levK, ?_⟩, ⟨P₀, rfl⟩, Subtype.ext ?_⟩
      · rw [Category.assoc, ← hψ', ← Category.assoc (K'.levK), ← Category.assoc, hP₀]; exact P.2
      · simp only [mapPt_coe, Category.assoc]; rw [← Category.assoc]; exact hP₀
    · rintro ⟨Q, ⟨Q₀, hQ₀⟩, hQ⟩
      refine ⟨Q₀, ?_⟩
      rw [← Category.assoc, hQ₀, ← hQ, mapPt_coe]

  haveI : IsProper E.f := E.bundle.proper
  haveI : IsSeparated (φ ≫ E'.f) := by rw [hφ]; infer_instance
  haveI : IsSeparated φ := IsSeparated.of_comp φ E'.f
  haveI : IsClosedImmersion K'.levK := K'.levK_closed
  haveI hKcl : IsClosedImmersion (K'.levK ≫ ψ') := by
    have : IsClosedImmersion ((K'.levK ≫ ψ') ≫ φ) := by rw [Category.assoc, hunivK']; infer_instance
    exact IsClosedImmersion.of_comp (K'.levK ≫ ψ') φ
  have hcomp : (K'.levK ≫ ψ') ≫ E.f = K'.levK ≫ E'.f := by rw [Category.assoc, hψ']
  obtain ⟨iFin, iFlat, iFP, hrank⟩ : ∃ (_ : IsFinite ((K'.levK ≫ ψ') ≫ E.f)) (_ : Flat ((K'.levK ≫ ψ') ≫ E.f))
      (_ : LocallyOfFinitePresentation ((K'.levK ≫ ψ') ≫ E.f)),
      ∀ s : ↥(Spec (CommRingCat.of S)), ((K'.levK ≫ ψ') ≫ E.f).finrank s = ℓ ^ 2 := by
    rw [hcomp]; exact ⟨K'.levK_finite, K'.levK_flat, K'.levK_finitePresentation, K'.levK_rank⟩

  let K : E.ExtraLevel ℓ :=
    { K := K'.K
      levK := K'.levK ≫ ψ'
      levK_closed := hKcl
      levK_sub := by
        intro T t P Q hP hQ
        obtain ⟨P₁, hP₁, rfl⟩ := (char t P).mp hP
        obtain ⟨Q₁, hQ₁, rfl⟩ := (char t Q).mp hQ
        obtain ⟨hm, hi⟩ := K'.levK_sub t P₁ Q₁ hP₁ hQ₁
        exact ⟨(char t _).mpr ⟨_, hm, hmulψ' t P₁ Q₁⟩,
          (char t _).mpr ⟨_, hi, hom_inv E'.L E.L t (mapPt ψ' hψ') (hmulψ' t) P₁⟩⟩
      levK_one := fun t => (char t _).mpr ⟨_, K'.levK_one t, hom_one E'.L E.L t (mapPt ψ' hψ') (hmulψ' t)⟩
      levK_torsion := by
        intro T t P hP
        obtain ⟨Q, hQ, rfl⟩ := (char t P).mp hP
        rw [← hom_nsmulPt E'.L E.L t (mapPt ψ' hψ') (hmulψ' t), K'.levK_torsion t Q hQ]
        exact hom_one E'.L E.L t (mapPt ψ' hψ') (hmulψ' t)
      levK_stable := by
        intro x T t P hP
        obtain ⟨Q, hQ, rfl⟩ := (char t P).mp hP
        exact (char t _).mpr ⟨_, K'.levK_stable x t Q hQ, hlinψ'_pt x t Q⟩
      levK_disjoint := by
        intro T t P hP hPl
        obtain ⟨Q, hQ, rfl⟩ := (char t P).mp hP
        have hQl : FactorsThrough E'.lev Q := by
          have := hlev t _ hPl
          rwa [hF1 t Q (K'.levK_torsion t Q hQ)] at this
        rw [K'.levK_disjoint t Q hQ hQl]
        exact hom_one E'.L E.L t (mapPt ψ' hψ') (hmulψ' t)
      levK_finite := iFin
      levK_flat := iFlat
      levK_finitePresentation := iFP
      levK_rank := hrank
      levK_fibre := by
        intro k _ _ sk hk
        obtain ⟨e', he'⟩ := K'.levK_fibre k sk hk
        let bij : {Q : SchemeHomOver (geomPoint k sk) E'.f // FactorsThrough K'.levK Q} ≃
            {P : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough (K'.levK ≫ ψ') P} :=
          { toFun := fun Q => ⟨mapPt ψ' hψ' Q.1, (char _ _).mpr ⟨Q.1, Q.2, rfl⟩⟩
            invFun := fun P => ⟨mapPt φ hφ P.1, by
              obtain ⟨Q, hQ, hQP⟩ := (char _ _).mp P.2
              rw [← hQP, hF1 _ Q (K'.levK_torsion _ Q hQ)]; exact hQ⟩
            left_inv := fun Q => Subtype.ext (hF1 _ Q.1 (K'.levK_torsion _ Q.1 Q.2))
            right_inv := fun P => Subtype.ext (by
              obtain ⟨Q, hQ, hQP⟩ := (char _ _).mp P.2
              show mapPt ψ' hψ' (mapPt φ hφ P.1) = P.1
              rw [← hQP, hF1 _ Q (K'.levK_torsion _ Q hQ)]) }
        refine ⟨e'.trans bij, fun x y => ?_⟩
        show mapPt ψ' hψ' (e' (x + y)).1 = E.L.mul _ (mapPt ψ' hψ' (e' x).1) (mapPt ψ' hψ' (e' y).1)
        rw [he', hmulψ'] }
  refine ⟨K, ?_, ?_⟩
  · intro T t P hP
    obtain ⟨Q, hQ, rfl⟩ := (char t P).mp hP
    rw [hF1 t Q (K'.levK_torsion t Q hQ)]; exact hQ
  · intro K₂ hK₂ T t P
    constructor
    · intro hP

      obtain ⟨g, hg⟩ := hK₂ (K₂.levK ≫ E.f) ⟨K₂.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
      simp only [mapPt_coe] at hg
      have hunivK₂ : K₂.levK ≫ φ ≫ ψ' = K₂.levK := by
        have htor := K₂.levK_torsion (K₂.levK ≫ E.f) ⟨K₂.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
        have := congrArg Subtype.val (hF2 _ _ htor)
        simpa only [mapPt_coe, Category.assoc] using this
      have hgK : g ≫ (K'.levK ≫ ψ') = K₂.levK := by rw [← Category.assoc, hg, Category.assoc, hunivK₂]
      haveI : IsClosedImmersion K₂.levK := K₂.levK_closed
      haveI : IsClosedImmersion (g ≫ (K'.levK ≫ ψ')) := by rw [hgK]; infer_instance
      haveI : IsClosedImmersion g := IsClosedImmersion.of_comp g (K'.levK ≫ ψ')
      haveI := iFin; haveI := iFlat; haveI := iFP
      haveI := K₂.levK_flat; haveI := K₂.levK_finitePresentation
      have hw : g ≫ ((K'.levK ≫ ψ') ≫ E.f) = K₂.levK ≫ E.f := by rw [← Category.assoc, hgK]
      haveI : IsIso g :=
        AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq g ((K'.levK ≫ ψ') ≫ E.f) (K₂.levK ≫ E.f) hw
          (fun s => by rw [K₂.levK_rank s, hrank s])
      obtain ⟨P₀, hP₀⟩ := hP
      refine ⟨P₀ ≫ inv g, ?_⟩
      rw [← hP₀, ← hgK, Category.assoc, IsIso.inv_hom_id_assoc]
    · intro hP
      have hP' := hK₂ t P hP
      have htor := K₂.levK_torsion t P hP
      exact (char t P).mpr ⟨_, hP', hF2 t P htor⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem (solution)
