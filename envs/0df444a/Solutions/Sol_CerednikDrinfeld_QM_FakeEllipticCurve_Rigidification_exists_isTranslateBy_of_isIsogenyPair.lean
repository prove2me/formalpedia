-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isTranslateBy_of_isIsogenyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/886c3540-f962-550b-b463-d02a0699afb1

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld.QM"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.Rigidification QM.FakeEllipticCurve QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback QM.FakeEllipticCurve.isPullbackVia_id"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.Rigidification FakeEllipticCurve.Rigidification.IsTranslateBy FakeEllipticCurve.Rigidification.residueLeg mapPt mapPt_coe FactorsThrough FakeEllipticCurve FakeEllipticCurve.IsIsogenyPair FakeEllipticCurve.PreservesLevel FakeEllipticCurve.IsPullbackVia FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback FakeEllipticCurve.isPullbackVia_id"
namespace TranslateExists
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

section BaseChange

variable {k₀ : Type} [CommRing k₀] {Bb : Type} [CommRing Bb] {ψb : k₀ →+* Bb}
  {A₀ : FakeEllipticCurve Λ N k₀} {Ab : FakeEllipticCurve Λ N Bb} {gA : Ab.A ⟶ A₀.A}
  (hsq : IsPullback gA Ab.f A₀.f (Spec.map (CommRingCat.ofHom ψb)))

noncomputable def bc (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f) : Ab.A ⟶ Ab.A :=
  hsq.lift (gA ≫ e) Ab.f (by rw [Category.assoc, he, hsq.w])

theorem bc_gA (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f) : bc hsq e he ≫ gA = gA ≫ e := hsq.lift_fst _ _ _

theorem bc_f (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f) : bc hsq e he ≫ Ab.f = Ab.f := hsq.lift_snd _ _ _

def gpt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (Q : SchemeHomOver t Ab.f) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom ψb)) A₀.f :=
  ⟨Q.1 ≫ gA, by rw [Category.assoc, hsq.w, ← Category.assoc, Q.2]⟩

@[scoped simp] theorem gpt_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (Q : SchemeHomOver t Ab.f) :
    (gpt hsq t Q).1 = Q.1 ≫ gA := rfl

include hsq in
theorem ginj {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (Q Q' : SchemeHomOver t Ab.f)
    (h : Q.1 ≫ gA = Q'.1 ≫ gA) : Q = Q' :=
  Subtype.ext (hsq.hom_ext h (by rw [Q.2, Q'.2]))

theorem gpt_mapPt_bc (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb))
    (Q : SchemeHomOver t Ab.f) : gpt hsq t (mapPt (bc hsq e he) (bc_f hsq e he) Q) = mapPt e he (gpt hsq t Q) := by
  apply Subtype.ext
  simp only [gpt_coe, mapPt_coe, Category.assoc, bc_gA]

variable (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver t' Ab.f),
    (Ab.L.mul t' P Q).1 ≫ gA =
      (A₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ψb))
        ⟨P.1 ≫ gA, by rw [Category.assoc, hsq.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ gA, by rw [Category.assoc, hsq.w, ← Category.assoc, Q.2]⟩).1)

include hmul in
theorem gpt_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver t Ab.f) :
    gpt hsq t (Ab.L.mul t P Q) = A₀.L.mul _ (gpt hsq t P) (gpt hsq t Q) := Subtype.ext (hmul t P Q)

include hmul in

theorem bc_mul (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f)
    (hehom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt e he (A₀.L.mul t P Q) = A₀.L.mul t (mapPt e he P) (mapPt e he Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver t Ab.f) :
    mapPt (bc hsq e he) (bc_f hsq e he) (Ab.L.mul t P Q) =
      Ab.L.mul t (mapPt (bc hsq e he) (bc_f hsq e he) P) (mapPt (bc hsq e he) (bc_f hsq e he) Q) := by
  apply ginj hsq
  have h1 := congrArg Subtype.val (gpt_mapPt_bc hsq e he t (Ab.L.mul t P Q))
  have h2 := congrArg Subtype.val (gpt_mul hsq hmul t (mapPt (bc hsq e he) (bc_f hsq e he) P) (mapPt (bc hsq e he) (bc_f hsq e he) Q))
  simp only [gpt_coe] at h1 h2
  rw [h1, h2, gpt_mul hsq hmul, hehom, gpt_mapPt_bc, gpt_mapPt_bc]

theorem bc_act (hact : ∀ x : ↥Λ, Ab.act x ≫ gA = gA ≫ A₀.act x) (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f)
    (heact : ∀ x : ↥Λ, A₀.act x ≫ e = e ≫ A₀.act x) (x : ↥Λ) :
    Ab.act x ≫ bc hsq e he = bc hsq e he ≫ Ab.act x := by
  apply hsq.hom_ext
  · rw [Category.assoc, bc_gA, ← Category.assoc, hact, Category.assoc, heact, ← Category.assoc, ← bc_gA hsq e he,
      Category.assoc, Category.assoc, hact]
  · rw [Category.assoc, bc_f, Ab.act_over, Category.assoc, Ab.act_over, bc_f]

theorem bc_comp_bc (e e' : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f) (he' : e' ≫ A₀.f = A₀.f) :
    bc hsq e he ≫ bc hsq e' he' = bc hsq (e ≫ e') (by rw [Category.assoc, he', he]) := by
  apply hsq.hom_ext
  · rw [Category.assoc, bc_gA, ← Category.assoc, bc_gA, bc_gA, Category.assoc]
  · rw [Category.assoc, bc_f, bc_f, bc_f]

theorem bc_act_eq (hact : ∀ x : ↥Λ, Ab.act x ≫ gA = gA ≫ A₀.act x) (x : ↥Λ) :
    bc hsq (A₀.act x) (A₀.act_over x) = Ab.act x := by
  apply hsq.hom_ext
  · rw [bc_gA, hact]
  · rw [bc_f, Ab.act_over]

theorem bc_lev (hvia : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA) (hsq' : hvia.1 = hsq)
    (e : A₀.A ⟶ A₀.A) (he : e ≫ A₀.f = A₀.f)
    (helev : FakeEllipticCurve.PreservesLevel A₀ A₀ e he)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (Q : SchemeHomOver t Ab.f) (hQ : FactorsThrough Ab.lev Q) :
    FactorsThrough Ab.lev (mapPt (bc hsq e he) (bc_f hsq e he) Q) := by
  obtain ⟨hg, hm, ha, hl⟩ := hvia
  cases hsq'
  obtain ⟨P₀, hP₀⟩ := hl t Q hQ
  have h1 : FactorsThrough A₀.lev (gpt hg t Q) := ⟨P₀, hP₀⟩
  have h2 := helev _ _ h1
  obtain ⟨P₁, hP₁⟩ := h2
  refine CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback ψb A₀ Ab gA hg hm hl t
    (mapPt (bc hg e he) (bc_f hg e he) Q) ⟨P₁, ?_⟩
  rw [hP₁, mapPt_coe, gpt_coe, mapPt_coe, Category.assoc, Category.assoc, bc_gA]

end BaseChange

end CerednikDrinfeld.QM.TranslateExists
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld.QM.TranslateExists"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair.CerednikDrinfeld"

open CerednikDrinfeld.QM.TranslateExists in
theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (eγ eγ' : A₀.A ⟶ A₀.A) (heγ : eγ ≫ A₀.f = A₀.f) (dγ : ℕ)
    (hpair : FakeEllipticCurve.IsIsogenyPair (r ^ dγ) A₀ A₀ eγ eγ')
    (hlev : FakeEllipticCurve.PreservesLevel A₀ A₀ eγ heγ)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) :
    ∃ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E,
      FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ eγ ϱ ρ₂ ∧
      (∀ (ℓ : ℕ) (K₀ : A₀.ExtraLevel ℓ),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
            FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt eγ heγ R)) →
        ∀ (C : E.ExtraLevel ℓ),
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
              (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) →
          (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ₂.Eb.f),
              (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ₂.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ₂.φ) ≫ ρ₂.gA)) := by
  classical

  have hvia := ϱ.isPullback_Ab
  obtain ⟨hsq, hmul, hact, hlv⟩ := ϱ.isPullback_Ab
  obtain ⟨heγ₀, heγ', mulγ, mulγ', actγ, actγ', compγ⟩ := hpair
  obtain ⟨hφ, hφ', mulφ, mulφ', actφ, actφ', compφ⟩ := ϱ.isIsogenyPair
  have hrd : (((r ^ dγ : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ ((r ^ dγ : ℕ) : ℤ)
  have hrd₀ : (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ ((r ^ ϱ.d : ℕ) : ℤ)

  obtain ⟨eb, eb', heb_f, heb'_f, heb_gA, heb'_gA, hmulb, hmulb', hactb, hactb', hee', he'e, hlevb⟩ :
      ∃ (eb eb' : ϱ.Ab.A ⟶ ϱ.Ab.A) (heb_f : eb ≫ ϱ.Ab.f = ϱ.Ab.f) (heb'_f : eb' ≫ ϱ.Ab.f = ϱ.Ab.f),
        eb ≫ ϱ.gA = ϱ.gA ≫ eγ ∧ eb' ≫ ϱ.gA = ϱ.gA ≫ eγ' ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ϱ.Ab.f),
          mapPt eb heb_f (ϱ.Ab.L.mul t P Q) = ϱ.Ab.L.mul t (mapPt eb heb_f P) (mapPt eb heb_f Q)) ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P Q : SchemeHomOver t ϱ.Ab.f),
          mapPt eb' heb'_f (ϱ.Ab.L.mul t P Q) = ϱ.Ab.L.mul t (mapPt eb' heb'_f P) (mapPt eb' heb'_f Q)) ∧
        (∀ x : ↥Λ, ϱ.Ab.act x ≫ eb = eb ≫ ϱ.Ab.act x) ∧ (∀ x : ↥Λ, ϱ.Ab.act x ≫ eb' = eb' ≫ ϱ.Ab.act x) ∧
        eb ≫ eb' = ϱ.Ab.act ⟨_, hrd⟩ ∧ eb' ≫ eb = ϱ.Ab.act ⟨_, hrd⟩ ∧
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (Q : SchemeHomOver t ϱ.Ab.f),
          FactorsThrough ϱ.Ab.lev Q → FactorsThrough ϱ.Ab.lev (mapPt eb heb_f Q)) := by
    refine ⟨bc hsq eγ heγ, bc hsq eγ' heγ', bc_f hsq eγ heγ, bc_f hsq eγ' heγ', bc_gA hsq eγ heγ, bc_gA hsq eγ' heγ',
      fun t P Q => bc_mul hsq hmul eγ heγ mulγ t P Q, fun t P Q => bc_mul hsq hmul eγ' heγ' mulγ' t P Q,
      bc_act hsq hact eγ heγ actγ, bc_act hsq hact eγ' heγ' actγ', ?_, ?_,
      fun t Q hQ => bc_lev hsq hvia rfl eγ heγ hlev t Q hQ⟩
    · rw [bc_comp_bc hsq eγ eγ' heγ heγ', ← bc_act_eq hsq hact]
      congr 1
      exact (compγ hrd).1
    · rw [bc_comp_bc hsq eγ' eγ heγ' heγ, ← bc_act_eq hsq hact]
      congr 1
      exact (compγ hrd).2

  have hφ₂ : (ϱ.φ ≫ eb) ≫ ϱ.Ab.f = ϱ.Eb.f := by rw [Category.assoc, heb_f, hφ]
  have hφ₂' : (eb' ≫ ϱ.φ') ≫ ϱ.Eb.f = ϱ.Ab.f := by rw [Category.assoc, hφ', heb'_f]
  have hprod1 : (((r ^ (ϱ.d + dγ) : ℕ) : ℚ) : ℍ[ℚ, a, b]) = ((r ^ ϱ.d : ℕ) : ℚ) * ((r ^ dγ : ℕ) : ℚ) := by
    push_cast; rw [pow_add]
  have hprod2 : (((r ^ (ϱ.d + dγ) : ℕ) : ℚ) : ℍ[ℚ, a, b]) = ((r ^ dγ : ℕ) : ℚ) * ((r ^ ϱ.d : ℕ) : ℚ) := by
    push_cast; rw [add_comm, pow_add]
  have hpair₂ : FakeEllipticCurve.IsIsogenyPair (r ^ (ϱ.d + dγ)) ϱ.Eb ϱ.Ab (ϱ.φ ≫ eb) (eb' ≫ ϱ.φ') := by
    refine ⟨hφ₂, hφ₂', ?_, ?_, ?_, ?_, ?_⟩
    · intro T t P Q
      have h1 : mapPt (ϱ.φ ≫ eb) hφ₂ (ϱ.Eb.L.mul t P Q) = mapPt eb heb_f (mapPt ϱ.φ hφ (ϱ.Eb.L.mul t P Q)) :=
        Subtype.ext (by simp only [mapPt_coe, Category.assoc])
      rw [h1, mulφ, hmulb]
      exact congrArg₂ _ (Subtype.ext (by simp only [mapPt_coe, Category.assoc])) (Subtype.ext (by simp only [mapPt_coe, Category.assoc]))
    · intro T t P Q
      have h1 : mapPt (eb' ≫ ϱ.φ') hφ₂' (ϱ.Ab.L.mul t P Q) = mapPt ϱ.φ' hφ' (mapPt eb' heb'_f (ϱ.Ab.L.mul t P Q)) :=
        Subtype.ext (by simp only [mapPt_coe, Category.assoc])
      rw [h1, hmulb', mulφ']
      exact congrArg₂ _ (Subtype.ext (by simp only [mapPt_coe, Category.assoc])) (Subtype.ext (by simp only [mapPt_coe, Category.assoc]))
    · intro x
      rw [← Category.assoc, actφ x, Category.assoc, hactb x, Category.assoc]
    · intro x
      rw [← Category.assoc, hactb' x, Category.assoc, actφ' x, Category.assoc]
    · intro hd
      have hmem1 : (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (((r ^ dγ : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← hprod1]; exact hd
      have hmem2 : (((r ^ dγ : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← hprod2]; exact hd
      constructor
      ·
        calc (ϱ.φ ≫ eb) ≫ eb' ≫ ϱ.φ' = ϱ.φ ≫ (eb ≫ eb') ≫ ϱ.φ' := by simp only [Category.assoc]
          _ = ϱ.φ ≫ ϱ.Ab.act ⟨_, hrd⟩ ≫ ϱ.φ' := by rw [hee']
          _ = ϱ.Eb.act ⟨_, hrd⟩ ≫ (ϱ.φ ≫ ϱ.φ') := by rw [← Category.assoc, ← actφ, Category.assoc]
          _ = ϱ.Eb.act ⟨_, hrd⟩ ≫ ϱ.Eb.act ⟨_, hrd₀⟩ := by rw [(compφ hrd₀).1]
          _ = ϱ.Eb.act ⟨_, hmem1⟩ := (ϱ.Eb.act_mul ⟨_, hrd₀⟩ ⟨_, hrd⟩ hmem1).symm
          _ = ϱ.Eb.act ⟨_, hd⟩ := by congr 1; exact Subtype.ext hprod1.symm
      · calc (eb' ≫ ϱ.φ') ≫ ϱ.φ ≫ eb = eb' ≫ (ϱ.φ' ≫ ϱ.φ) ≫ eb := by simp only [Category.assoc]
          _ = eb' ≫ ϱ.Ab.act ⟨_, hrd₀⟩ ≫ eb := by rw [(compφ hrd₀).2]
          _ = ϱ.Ab.act ⟨_, hrd₀⟩ ≫ (eb' ≫ eb) := by rw [← Category.assoc, ← hactb', Category.assoc]
          _ = ϱ.Ab.act ⟨_, hrd₀⟩ ≫ ϱ.Ab.act ⟨_, hrd⟩ := by rw [he'e]
          _ = ϱ.Ab.act ⟨_, hmem2⟩ := (ϱ.Ab.act_mul ⟨_, hrd⟩ ⟨_, hrd₀⟩ hmem2).symm
          _ = ϱ.Ab.act ⟨_, hd⟩ := by congr 1; exact Subtype.ext hprod2.symm
  have hlev₂ : FakeEllipticCurve.PreservesLevel ϱ.Eb ϱ.Ab (ϱ.φ ≫ eb) hφ₂ := by
    intro T t P hP
    have h1 : mapPt (ϱ.φ ≫ eb) hφ₂ P = mapPt eb heb_f (mapPt ϱ.φ hφ P) := Subtype.ext (by simp only [mapPt_coe, Category.assoc])
    rw [h1]
    exact hlevb t _ (ϱ.preservesLevel t P hP)
  let ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E :=
    { Eb := ϱ.Eb, gb := ϱ.gb, isPullback_Eb := ϱ.isPullback_Eb, Ab := ϱ.Ab, gA := ϱ.gA, isPullback_Ab := hvia,
      d := ϱ.d + dγ, φ := ϱ.φ ≫ eb, φ' := eb' ≫ ϱ.φ', φ_over := hφ₂, isIsogenyPair := hpair₂, preservesLevel := hlev₂ }
  refine ⟨ρ₂, ?_, ?_⟩
  ·
    refine ⟨𝟙 _, 𝟙 _, ⟨?_, Category.id_comp _, ?_, Category.id_comp _⟩, eb, heb_gA, heb_f, 0, 0, ?_⟩
    · exact CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ϱ.Eb
    · exact CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ ϱ.Ab
    · change 𝟙 _ ≫ ϱ.φ ≫ eb ≫ ϱ.Ab.act _ = (ϱ.φ ≫ eb) ≫ 𝟙 _ ≫ ϱ.Ab.act _
      simp only [Category.id_comp, Category.assoc]
  ·
    intro ℓ K₀ hstab C hC T t' R hR
    obtain ⟨Q₀, hQ₀⟩ := hC t' R hR
    have hRA : ((R.1 ≫ ϱ.φ) ≫ ϱ.gA) ≫ A₀.f =
        t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) := by
      rw [Category.assoc, Category.assoc, hsq.w, ← Category.assoc, ← Category.assoc, Category.assoc R.1, hφ, R.2]
    have h1 : FactorsThrough K₀.levK (⟨(R.1 ≫ ϱ.φ) ≫ ϱ.gA, hRA⟩ : SchemeHomOver _ A₀.f) := ⟨Q₀, hQ₀⟩
    obtain ⟨Q₁, hQ₁⟩ := hstab _ _ h1
    refine ⟨Q₁, ?_⟩
    rw [hQ₁, mapPt_coe]
    change ((R.1 ≫ ϱ.φ) ≫ ϱ.gA) ≫ eγ = (R.1 ≫ ϱ.φ ≫ eb) ≫ ϱ.gA
    simp only [Category.assoc, heb_gA]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isTranslateBy_of_isIsogenyPair (solution)
