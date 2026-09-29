-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.forall_preservesExtraLevel_iff_mem_inf_map_conj_of_heckeDictionary_star_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/92e25e30-4f1b-54f0-9481-9de93e504512

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_preservesExtraLevel_iff_mem_inf_map_conj_of_heckeDictionary_star_of_comp_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField

namespace StabDictAux

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

variable {S : Type} [CommRing S]

section Pts

variable {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem nsmulPt_zero {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) :
    nsmulPt L t 0 P = L.one t := rfl

theorem nsmulPt_succ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) (n : ℕ) :
    nsmulPt L t (n + 1) P = L.mul t (nsmulPt L t n P) P := rfl

theorem nsmulPt_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f) (n : ℕ) :
    nsmulPt L t n P = (letI := L.pointGroup t; P ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [nsmulPt_zero, pow_zero]; rfl
  | succ n ih => rw [nsmulPt_succ, pow_succ, ih]; rfl

theorem eq_one_of_nsmulPt_eq_one_of_coprime {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t f) (m n : ℕ) (hmn : Nat.Coprime m n)
    (hm : nsmulPt L t m P = L.one t) (hn : nsmulPt L t n P = L.one t) : P = L.one t := by
  letI := L.pointGroup t
  have hm' : P ^ m = 1 := by rw [← nsmulPt_eq_pow]; exact hm
  have hn' : P ^ n = 1 := by rw [← nsmulPt_eq_pow]; exact hn
  have h1 : orderOf P ∣ Nat.gcd m n := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hn')
  rw [Nat.Coprime.gcd_eq_one hmn, Nat.dvd_one] at h1
  exact orderOf_eq_one_iff.mp h1

theorem mem_of_nsmulPt_mem_of_coprime {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (K : SchemeHomOver t f → Prop) (hK1 : K (L.one t)) (hKmul : ∀ P Q, K P → K Q → K (L.mul t P Q))
    (P : SchemeHomOver t f) (ℓ m : ℕ) (hℓ : 1 < ℓ) (hcop : Nat.Coprime m ℓ)
    (htors : nsmulPt L t ℓ P = L.one t) (hm : K (nsmulPt L t m P)) : K P := by
  letI := L.pointGroup t
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ
  have hpow : ∀ (n : ℕ) (Q : SchemeHomOver t f), K Q → K (Q ^ n) := by
    intro n Q hQ
    induction n with
    | zero => rw [pow_zero]; exact hK1
    | succ n ih => rw [pow_succ]; exact hKmul _ _ ih hQ
  have hℓ' : P ^ ℓ = 1 := by rw [← nsmulPt_eq_pow]; exact htors
  have key : P = P ^ (m * u) := by
    conv_rhs => rw [← Nat.div_add_mod (m * u) ℓ, hu, pow_add, pow_one, pow_mul, hℓ', one_pow, one_mul]
  rw [key, pow_mul]
  exact hpow u _ (by rw [← nsmulPt_eq_pow]; exact hm)

variable {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of S)} (L' : RelativeGroupLaw S f')
  (φ : A ⟶ A') (hφ : φ ≫ f' = f)

theorem mapPt_one
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : mapPt φ hφ (L.one t) = L'.one t :=
  eq_one_of_mul_self L' t _ (by rw [← hhom, L.one_mul])

theorem mapPt_nsmulPt
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => rw [nsmulPt_zero, nsmulPt_zero]; exact mapPt_one L L' φ hφ hhom t
  | succ n ih => rw [nsmulPt_succ, nsmulPt_succ, hhom, ih]

omit L L' in
theorem mapPt_comp {A'' : Scheme.{0}} {f'' : A'' ⟶ Spec (CommRingCat.of S)} (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    (h : (φ ≫ ψ) ≫ f'' = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (by simp only [mapPt_coe, Category.assoc])

omit L L' φ hφ in
theorem mapPt_id (h : 𝟙 A ≫ f = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt (𝟙 A) h P = P :=
  Subtype.ext (by simp only [mapPt_coe, Category.comp_id])

omit L L' φ hφ in
theorem mapPt_congr {φ₁ φ₂ : A ⟶ A'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ f' = f) (h₂ : φ₂ ≫ f' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    mapPt φ₁ h₁ P = mapPt φ₂ h₂ P := by
  subst h; rfl

end Pts

section FEC

open scoped Quaternion

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem pushPt_act_natCast (E : FakeEllipticCurve Λ N S) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (n : ℕ) (x : ↥Λ) (hx : (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    mapPt (E.act x) (E.act_over x) P = nsmulPt E.L t n P := by
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := Subtype.ext (by rw [hx]; simp)
    subst hx0
    have h := E.act_add 0 0 t P
    dsimp only [pushPt] at h
    rw [add_zero] at h
    rw [nsmulPt_zero]
    exact eq_one_of_mul_self E.L t _ h.symm
  | succ n ih =>
    set n' : ↥Λ := ⟨((n : ℤ) : ℚ), hΛℤ n⟩ with hn'
    set one' : ↥Λ := ⟨((1 : ℤ) : ℚ), hΛℤ 1⟩ with hone'
    have hx' : x = n' + one' := Subtype.ext (by
      rw [hx, Submodule.coe_add, hn', hone']
      push_cast
      abel)
    subst hx'
    have hadd := E.act_add n' one' t P
    dsimp only [pushPt] at hadd
    rw [hadd, ih n' (by rw [hn']; push_cast; rfl), nsmulPt_succ]
    have hone : E.act one' = 𝟙 E.A := by
      have : one' = ⟨1, by simpa using hΛℤ 1⟩ := Subtype.ext (by rw [hone']; push_cast; rfl)
      rw [this]; exact E.act_one _
    show E.L.mul t _ (mapPt (E.act one') (E.act_over one') P) = _
    rw [mapPt_congr hone (E.act_over one') (Category.id_comp _), mapPt_id]

theorem ExtraLevel.nsmulPt_mem (E : FakeEllipticCurve Λ N S) {ℓ : ℕ} (K : E.ExtraLevel ℓ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f)
    (hP : FactorsThrough K.levK P) (n : ℕ) : FactorsThrough K.levK (nsmulPt E.L t n P) := by
  induction n with
  | zero => rw [nsmulPt_zero]; exact K.levK_one t
  | succ n ih => rw [nsmulPt_succ]; exact (K.levK_sub t _ _ ih hP).1

theorem factorsThrough_levK_mapPt_of_comp_eq
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E E' : FakeEllipticCurve Λ N S) {ℓ : ℕ} (K : E.ExtraLevel ℓ)
    (as : E.A ⟶ E'.A) (has : as ≫ E'.f = E.f) (as' : E'.A ⟶ E.A) (has' : as' ≫ E.f = E'.f)
    (hK : FakeEllipticCurve.IsLevelIsogenyVia ℓ ⟨E, K⟩ E' as has as' has')
    (d : ℕ) (hd : Nat.Coprime ℓ d) (bs : E'.A ⟶ E.A) (hbs : bs ≫ E.f = E'.f) (bs' : E.A ⟶ E'.A)
    (hbsI : FakeEllipticCurve.IsIsogenyPair d E' E bs bs')
    (φ ψ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) (hψ : ψ ≫ E.f = E.f)
    (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt ψ hψ (E.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hcomm : φ ≫ (as ≫ bs) = (as ≫ bs) ≫ ψ) :
    ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P → FactorsThrough K.levK (mapPt φ hφ P) := by
  obtain ⟨has_hom, -, -, -, -, hker, -⟩ := hK
  obtain ⟨hbs₀, hbs'₀, hbs_hom, hbs'_hom, -, -, hbsbs'⟩ := hbsI
  have hdΛ : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ d
  have hcomp : bs ≫ bs' = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdΛ⟩ := (hbsbs' hdΛ).1
  have habs : (as ≫ bs) ≫ E.f = E.f := by rw [Category.assoc, hbs, has]
  intro T t P hP
  have h1 : mapPt as has P = E'.L.one t := (hker t P).2 hP
  apply (hker t _).1
  have hQ'ℓ : nsmulPt E'.L t ℓ (mapPt as has (mapPt φ hφ P)) = E'.L.one t := by
    rw [← mapPt_nsmulPt E.L E'.L as has has_hom, ← mapPt_nsmulPt E.L E.L φ hφ hφhom, K.levK_torsion t P hP,
      mapPt_one E.L E.L φ hφ hφhom, mapPt_one E.L E'.L as has has_hom]
  have hbsQ' : mapPt bs hbs (mapPt as has (mapPt φ hφ P)) = E.L.one t := by
    rw [← mapPt_comp as has bs hbs habs, ← mapPt_comp φ hφ (as ≫ bs) habs (by rw [Category.assoc, habs, hφ]),
      mapPt_congr hcomm _ (by rw [Category.assoc, hψ, habs]), mapPt_comp (as ≫ bs) habs ψ hψ,
      mapPt_comp as has bs hbs habs, h1, mapPt_one E'.L E.L bs hbs hbs_hom, mapPt_one E.L E.L ψ hψ hψhom]
  have hQ'd : nsmulPt E'.L t d (mapPt as has (mapPt φ hφ P)) = E'.L.one t := by
    rw [← pushPt_act_natCast E' hΛℤ d ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdΛ⟩ rfl t]
    show mapPt (E'.act _) (E'.act_over _) _ = _
    rw [mapPt_congr hcomp.symm (E'.act_over _) (by rw [Category.assoc, hbs'₀, hbs₀]),
      mapPt_comp bs hbs₀ bs' hbs'₀, hbsQ', mapPt_one E.L E'.L bs' hbs'₀ hbs'_hom]
  exact eq_one_of_nsmulPt_eq_one_of_coprime E'.L t _ ℓ d hd hQ'ℓ hQ'd

theorem factorsThrough_levK_of_nsmulPt_eq_one_of_mapPt_comp_eq_one
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E E' : FakeEllipticCurve Λ N S) {ℓ : ℕ} (K : E.ExtraLevel ℓ)
    (as : E.A ⟶ E'.A) (has : as ≫ E'.f = E.f) (as' : E'.A ⟶ E.A) (has' : as' ≫ E.f = E'.f)
    (hK : FakeEllipticCurve.IsLevelIsogenyVia ℓ ⟨E, K⟩ E' as has as' has')
    (d : ℕ) (hd : Nat.Coprime ℓ d) (bs : E'.A ⟶ E.A) (hbs : bs ≫ E.f = E'.f) (bs' : E.A ⟶ E'.A)
    (hbsI : FakeEllipticCurve.IsIsogenyPair d E' E bs bs') (habs : (as ≫ bs) ≫ E.f = E.f) :
    ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      nsmulPt E.L t ℓ P = E.L.one t → mapPt (as ≫ bs) habs P = E.L.one t → FactorsThrough K.levK P := by
  obtain ⟨has_hom, -, -, -, -, hker, -⟩ := hK
  obtain ⟨hbs₀, hbs'₀, hbs_hom, hbs'_hom, -, -, hbsbs'⟩ := hbsI
  have hdΛ : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by exact_mod_cast hΛℤ d
  have hcomp : bs ≫ bs' = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdΛ⟩ := (hbsbs' hdΛ).1
  intro T t P hPℓ hPk
  apply (hker t _).1
  have hQ'ℓ : nsmulPt E'.L t ℓ (mapPt as has P) = E'.L.one t := by
    rw [← mapPt_nsmulPt E.L E'.L as has has_hom, hPℓ, mapPt_one E.L E'.L as has has_hom]
  have hbsQ' : mapPt bs hbs (mapPt as has P) = E.L.one t := by
    rw [← mapPt_comp as has bs hbs habs]; exact hPk
  have hQ'd : nsmulPt E'.L t d (mapPt as has P) = E'.L.one t := by
    rw [← pushPt_act_natCast E' hΛℤ d ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdΛ⟩ rfl t]
    show mapPt (E'.act _) (E'.act_over _) _ = _
    rw [mapPt_congr hcomp.symm (E'.act_over _) (by rw [Category.assoc, hbs'₀, hbs₀]),
      mapPt_comp bs hbs₀ bs' hbs'₀, hbsQ', mapPt_one E.L E'.L bs' hbs'₀ hbs'_hom]
  exact eq_one_of_nsmulPt_eq_one_of_coprime E'.L t _ ℓ d hd hQ'ℓ hQ'd

theorem nsmulPt_mul (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t E.f) (m n : ℕ) : nsmulPt E.L t (m * n) P = nsmulPt E.L t m (nsmulPt E.L t n P) := by
  letI := E.L.pointGroup t
  rw [nsmulPt_eq_pow, nsmulPt_eq_pow, nsmulPt_eq_pow, mul_comm, pow_mul]

theorem nsmulPt_one' (E : FakeEllipticCurve Λ N S) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) :
    nsmulPt E.L t n (E.L.one t) = E.L.one t := by
  letI := E.L.pointGroup t
  rw [nsmulPt_eq_pow]; exact one_pow n

omit S in
theorem nrd_smul (c : ℚ) (x : ℍ[ℚ, a, b]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.nrd_mk, QuaternionAlgebra.smul_mk, smul_eq_mul]
  ring

end FEC

end StabDictAux

open scoped Quaternion

theorem solution
    {r rbar N n : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)

    (hX₀ : X₀.HasHeight 4) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (hE1 :
      (∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ)))
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (hE1sc :
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ i : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c * ((r ^ i : ℕ) : ℤ) : ℤ) : ℚ), hΛℤ _⟩))

    (hE1' :
      (∀ (γ : ↥Γt), (∃ (i c : ℕ), 0 < c ∧ e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c : ℤ) : ℚ), hΛℤ _⟩) →
          ∃ c : ℚ, ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])))

    (hE2 :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, ∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (hE3 :
      (∀ P₀ : A₀.FullLevel n, ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b]))))

    (hE4 :
      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k]
          (A : FakeEllipticCurve Λ N k) (gA : A.A ⟶ A₀.A),
          FakeEllipticCurve.IsPullbackVia (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k) A₀ A gA →
          (∀ (φ ψ : A.A ⟶ A.A) (d : ℕ) (hφ : φ ≫ A.f = A.f),
              FakeEllipticCurve.IsIsogenyPair (r ^ d) A A φ ψ → FakeEllipticCurve.PreservesLevel A A φ hφ →
              ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)))

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
    (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
    (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)

    (hE5a : ∀ x : ↥R₂,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
          mapPt (ê x) (hê x) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê x) (hê x) P) (mapPt (ê x) (hê x) Q)) ∧
      (∀ m : ↥Λ, A₀.act m ≫ ê x = ê x ≫ A₀.act m) ∧
      FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))

    (hE5one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
    (hE5mul : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
      ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
    (hE5int : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

    (hE5c : ∀ (x y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (x : ℍ[ℚ, a₁, b₁]) → nrd (x : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
      ê y ≫ ê x = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩)

    (hE5d : ∀ (γ : ↥Γt) (x : ↥R₂) (k : ℕ),
      (x : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
      ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê x ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (hE5e : ∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
        (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
        (∀ x : ↥R₂, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (ê x) (hê x) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (hE5g : ∀ z : ↥R₂, star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂)

    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (R₂' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂' : R₂' ≤ Λ₁s) (hR₂'o : IsOrder R₂')
    (hR₂'r : ∀ z : ↥Λ₁s, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) ∈ R₂') (hR₂R₂' : R₂ ≤ R₂')
    (ê' : ↥R₂' → (A₀.A ⟶ A₀.A)) (hê' : ∀ z, ê' z ≫ A₀.f = A₀.f)
    (hE6a : ∀ z : ↥R₂',
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
          mapPt (ê' z) (hê' z) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê' z) (hê' z) P) (mapPt (ê' z) (hê' z) Q)) ∧
      (∀ m : ↥Λ, A₀.act m ≫ ê' z = ê' z ≫ A₀.act m))
    (hE6one : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂', ê' ⟨1, h⟩ = 𝟙 A₀.A)
    (hE6mul : ∀ (z y : ↥R₂') (h : (z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂'),
      ê' ⟨(z : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê' y ≫ ê' z)
    (hE6int : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂'), ê' ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)
    (hE6c : ∀ (z y : ↥R₂') (nz : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (z : ℍ[ℚ, a₁, b₁]) → nrd (z : ℍ[ℚ, a₁, b₁]) = (nz : ℚ) →
      ê' y ≫ ê' z = A₀.act ⟨((nz : ℤ) : ℚ), hΛℤ nz⟩)
    (hE6d : ∀ z : ↥R₂, ê' ⟨(z : ℍ[ℚ, a₁, b₁]), hR₂R₂' z.2⟩ = ê z)
    (hE6star : ∀ z : ↥R₂', star (z : ℍ[ℚ, a₁, b₁]) ∈ R₂')
    (hE6inj : ∀ z y : ↥R₂', ê' z = ê' y → z = y)
    (hE6f : ∀ (q : ℕ), q.Prime → q ≠ r → ∀ z : ↥R₂',
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
          nsmulPt A₀.L t q P = A₀.L.one t → mapPt (ê' z) (hê' z) P = A₀.L.one t) →
      ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) • (z : ℍ[ℚ, a₁, b₁]) = (q : ℚ) • (y : ℍ[ℚ, a₁, b₁]))

    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ℓ : HeckeTower.AwayPrime r rbar) (s : (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs :
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (C₀ : A₀.ExtraLevel (ℓ.1 : ℕ)) (A₀s : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (as : A₀.A ⟶ A₀s.A) (has : as ≫ A₀s.f = A₀.f) (as' : A₀s.A ⟶ A₀.A) (has' : as' ≫ A₀.f = A₀s.f)
    (ks : ℕ) (bs : A₀s.A ⟶ A₀.A) (hbs : bs ≫ A₀.f = A₀s.f) (bs' : A₀.A ⟶ A₀s.A) (habs : (as ≫ bs) ≫ A₀.f = A₀.f)
    (hCs : FakeEllipticCurve.IsLevelIsogenyVia (ℓ.1 : ℕ) ⟨A₀, C₀⟩ A₀s as has as' has')
    (hbsI : FakeEllipticCurve.IsIsogenyPair (r ^ ks) A₀s A₀ bs bs') (hbsL : FakeEllipticCurve.PreservesLevel A₀s A₀ bs hbs)
    (hH2s : (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧

          (∃ (εs : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k_s : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ v : Fin 2 → B', (∀ i, v i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εs : MvFormalGroup.End X₀.F).toPowerSeries i) v) =
                  mapPt (as ≫ bs) habs (θ₀ B' v)) ∧
              E₀ εs = ((r : K₀) ^ k_s) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))))

    (ms : ℕ) (hms : (((r ^ ms : ℕ) : ℚ) • star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ∈ R₂)
    (hH3s : as ≫ bs = ê ⟨((r ^ ms : ℕ) : ℚ) • star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hms⟩) :
    ∀ γ : ↥Γt,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
          FactorsThrough C₀.levK P → FactorsThrough C₀.levK (mapPt (e γ) (he γ) P)) ↔
        (γ : (ℍ[ℚ, a₁, b₁])ˣ) ∈ Γt ⊓ Γt.map (MulAut.conj s).toMonoidHom := by

  classical

  have hℓP : (ℓ.1 : ℕ).Prime := ℓ.1.prop
  have hℓ1 : 1 < (ℓ.1 : ℕ) := hℓP.one_lt
  have hℓ0 : ((ℓ.1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓP.ne_zero
  have hrP : r.Prime := Fact.out
  have hℓr : Nat.Coprime (ℓ.1 : ℕ) r := (Nat.coprime_primes hℓP hrP).mpr ℓ.2.1
  have hR₁o : IsOrder R₁ := hR₁.isOrder

  have hsat : ∀ δ : ↥Γt, ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₂ := by
    intro δ
    have hmem := (CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq R₁ R₁ hR₁o hR₁o
      r v hv (fun _ _ => rfl)).1 (δ : (ℍ[ℚ, a₁, b₁])ˣ)
    obtain ⟨K, -, hK, -⟩ := hmem.1 ((hΓt _).1 δ.2)
    obtain ⟨c, hc⟩ := hR₂r ⟨_, hK⟩
    refine ⟨c + K, ?_⟩
    have : ((r ^ (c + K) : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) =
        ((r ^ c : ℕ) : ℚ) • (((r ^ K : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := by
      rw [smul_smul]; congr 1; push_cast; ring
    rw [this]; exact hc

  have hnsmul : ∀ (n : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ R₂ → ((n : ℕ) : ℚ) • y ∈ R₂ := by
    intro n y hy; rw [Nat.cast_smul_eq_nsmul]; exact R₂.toAddSubmonoid.nsmul_mem hy n
  intro γ
  constructor
  ·
    intro hpres
    refine Subgroup.mem_inf.mpr ⟨γ.2, ?_⟩
    obtain ⟨k, hγk⟩ := hsat γ
    set xs : ↥R₂ := ⟨((r ^ ms : ℕ) : ℚ) • star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hms⟩ with hxs
    have hxs'mem : ((r ^ ms : ℕ) : ℚ) • ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₂ := by
      have := hE5g xs
      rwa [hxs, QuaternionAlgebra.star_smul, star_star] at this
    set xs' : ↥R₂ := ⟨((r ^ ms : ℕ) : ℚ) • ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hxs'mem⟩ with hxs'
    set xγ : ↥R₂ := ⟨((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hγk⟩ with hxγ
    have habs' : (as ≫ bs) ≫ A₀.f = A₀.f := habs

    obtain ⟨i, j, hij⟩ := hE5d γ xγ k rfl
    obtain ⟨⟨hφ', -, heγ_hom, -⟩, -⟩ := hE1 γ
    have hrj : Nat.Coprime (r ^ j) (ℓ.1 : ℕ) := Nat.Coprime.pow_left _ hℓr.symm
    have hpresê : ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})))
        (P : SchemeHomOver t A₀.f), FactorsThrough C₀.levK P → FactorsThrough C₀.levK (mapPt (ê xγ) (hê xγ) P) := by
      intro T t P hP
      refine StabDictAux.mem_of_nsmulPt_mem_of_coprime A₀.L t (fun Q => FactorsThrough C₀.levK Q) (C₀.levK_one t)
        (fun P Q hP hQ => (C₀.levK_sub t P Q hP hQ).1) _ (ℓ.1 : ℕ) (r ^ j) hℓ1 hrj ?_ ?_
      · rw [← StabDictAux.mapPt_nsmulPt A₀.L A₀.L (ê xγ) (hê xγ) (hE5a xγ).1, C₀.levK_torsion t P hP,
          StabDictAux.mapPt_one A₀.L A₀.L (ê xγ) (hê xγ) (hE5a xγ).1]
      · rw [← StabDictAux.pushPt_act_natCast A₀ hΛℤ (r ^ j) ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ (by push_cast; rfl) t]
        show FactorsThrough C₀.levK (mapPt (A₀.act _) (A₀.act_over _) (mapPt (ê xγ) (hê xγ) P))
        rw [← StabDictAux.mapPt_comp (ê xγ) (hê xγ) (A₀.act _) (A₀.act_over _) (by rw [Category.assoc, A₀.act_over, hê]),
          StabDictAux.mapPt_congr hij.symm _ (by rw [Category.assoc, A₀.act_over, he]),
          StabDictAux.mapPt_comp (e γ) (he γ) (A₀.act _) (A₀.act_over _)]
        exact C₀.levK_stable _ t _ (hpres t P hP)

    have hm1 : (xs : ℍ[ℚ, a₁, b₁]) * (xγ : ℍ[ℚ, a₁, b₁]) ∈ R₂ := hR₂o.mul_mem xs.2 xγ.2
    have hm2 : (xs : ℍ[ℚ, a₁, b₁]) * (xγ : ℍ[ℚ, a₁, b₁]) * (xs' : ℍ[ℚ, a₁, b₁]) ∈ R₂ := hR₂o.mul_mem hm1 xs'.2
    have hêz : ê ⟨_, hm2⟩ = ê xs' ≫ (ê xγ ≫ ê xs) := by
      rw [hE5mul ⟨_, hm1⟩ xs' hm2, hE5mul xs xγ hm1]

    have hnrdxs : nrd (xs : ℍ[ℚ, a₁, b₁]) = (((r ^ ms * r ^ ms * (ℓ.1 : ℕ) : ℕ) : ℤ) : ℚ) := by
      rw [hxs]; push_cast
      rw [StabDictAux.nrd_smul, QuaternionAlgebra.nrd_star, hs.2.2.2]; ring
    have hpair : ê xs' ≫ ê xs = A₀.act ⟨(((r ^ ms * r ^ ms * (ℓ.1 : ℕ) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ :=
      hE5c xs xs' _ (by rw [hxs', hxs, QuaternionAlgebra.star_smul, star_star]) hnrdxs

    have hkill : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})))
        (P : SchemeHomOver t A₀.f), nsmulPt A₀.L t (ℓ.1 : ℕ) P = A₀.L.one t →
        mapPt (ê' ⟨_, hR₂R₂' hm2⟩) (hê' _) P = A₀.L.one t := by
      intro T t P hP
      rw [StabDictAux.mapPt_congr (hE6d ⟨_, hm2⟩) (hê' _) (hê _), StabDictAux.mapPt_congr hêz (hê _)
        (by rw [Category.assoc, Category.assoc, hê, hê, hê]),
        StabDictAux.mapPt_comp (ê xs') (hê xs') (ê xγ ≫ ê xs) (by rw [Category.assoc, hê, hê]),
        StabDictAux.mapPt_comp (ê xγ) (hê xγ) (ê xs) (hê xs)]

      have hP₁ : FactorsThrough C₀.levK (mapPt (ê xs') (hê xs') P) := by
        refine StabDictAux.factorsThrough_levK_of_nsmulPt_eq_one_of_mapPt_comp_eq_one hΛℤ A₀ A₀s C₀ as has as' has'
          hCs (r ^ ks) (Nat.Coprime.pow_right _ hℓr) bs hbs bs' hbsI habs' t _ ?_ ?_
        · rw [← StabDictAux.mapPt_nsmulPt A₀.L A₀.L (ê xs') (hê xs') (hE5a xs').1, hP,
            StabDictAux.mapPt_one A₀.L A₀.L (ê xs') (hê xs') (hE5a xs').1]
        · rw [StabDictAux.mapPt_congr hH3s habs' (hê xs), ← StabDictAux.mapPt_comp (ê xs') (hê xs') (ê xs) (hê xs)
            (by rw [Category.assoc, hê, hê]), StabDictAux.mapPt_congr hpair _ (A₀.act_over _),
            StabDictAux.pushPt_act_natCast A₀ hΛℤ (r ^ ms * r ^ ms * (ℓ.1 : ℕ))
              ⟨(((r ^ ms * r ^ ms * (ℓ.1 : ℕ) : ℕ) : ℤ) : ℚ), hΛℤ _⟩ (by push_cast; rfl) t,
            StabDictAux.nsmulPt_mul, hP, StabDictAux.nsmulPt_one']

      have hP₂ := hpresê t _ hP₁
      obtain ⟨-, -, -, -, -, hker, -⟩ := hCs
      obtain ⟨hbs₀, -, hbs_hom, -⟩ := hbsI
      rw [StabDictAux.mapPt_congr hH3s.symm (hê xs) habs', StabDictAux.mapPt_comp as has bs hbs habs',
        (hker t _).2 hP₂, StabDictAux.mapPt_one A₀s.L A₀.L bs hbs hbs_hom]
    obtain ⟨K, y, hKy⟩ := hE6f (ℓ.1 : ℕ) hℓP ℓ.2.1 ⟨_, hR₂R₂' hm2⟩ hkill

    have hint : ∃ (K : ℕ) (y : ↥Λ₁s), ((r ^ K : ℕ) : ℚ) •
        (star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
          ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) = ((ℓ.1 : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) := by
      refine ⟨K + ms + k + ms, y, ?_⟩
      rw [← hKy]
      simp only [hxs, hxγ, hxs', Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      congr 1; push_cast; ring
    exact CerednikDrinfeld.CosetGraph.mem_map_conj_of_mem_awayUnits_of_exists_pow_smul_star_mul_mul_eq_smul hrr hrN hrbarN hN hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ v hv
      Γt hΓt Λ₁s hΛ₁s hR₁Λ₁s htwin n₁ hn₁ hS₁ ℓ s sf hs γ γ.2 hint
  ·
    intro hγ
    obtain ⟨-, hγ'⟩ := Subgroup.mem_inf.mp hγ
    obtain ⟨δ₀, hδ₀, hconj⟩ := Subgroup.mem_map.mp hγ'
    set δ : ↥Γt := ⟨δ₀, hδ₀⟩ with hδ

    have hγs : ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * (s : ℍ[ℚ, a₁, b₁]) =
        (s : ℍ[ℚ, a₁, b₁]) * ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) := by
      have h1 : s * δ₀ = (γ : (ℍ[ℚ, a₁, b₁])ˣ) * s := by
        rw [← hconj]; simp [MulAut.conj_apply]
      have h2 := congrArg (fun u : (ℍ[ℚ, a₁, b₁])ˣ => (u : ℍ[ℚ, a₁, b₁])) h1
      simp only [Units.val_mul] at h2
      rw [hδ]; exact h2.symm

    set σ : ℍ[ℚ, a₁, b₁] := (s : ℍ[ℚ, a₁, b₁]) with hσ
    have hnrd : nrd σ = ((ℓ.1 : ℕ) : ℚ) := hs.2.2.2
    have hkey : star σ * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) =
        ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * star σ := by
      have e1 : star σ * (((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * σ) * star σ =
          star σ * (σ * ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * star σ := by rw [hγs]
      have e2 : (((ℓ.1 : ℕ) : ℚ)) • (star σ * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) =
          (((ℓ.1 : ℕ) : ℚ)) • (((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * star σ) := by
        calc (((ℓ.1 : ℕ) : ℚ)) • (star σ * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]))
            = (star σ * ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * ((((ℓ.1 : ℕ) : ℚ) : ℚ) : ℍ[ℚ, a₁, b₁]) := by
              rw [QuaternionAlgebra.mul_coe_eq_smul]
          _ = star σ * (((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * σ) * star σ := by
              rw [← hnrd, ← QuaternionAlgebra.mul_star_eq_coe_nrd]; simp only [mul_assoc]
          _ = star σ * (σ * ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) * star σ := e1
          _ = ((((ℓ.1 : ℕ) : ℚ) : ℚ) : ℍ[ℚ, a₁, b₁]) * (((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * star σ) := by
              rw [← hnrd, ← QuaternionAlgebra.star_mul_eq_coe_nrd]; simp only [mul_assoc]
          _ = (((ℓ.1 : ℕ) : ℚ)) • (((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * star σ) := by
              rw [QuaternionAlgebra.coe_mul_eq_smul]
      exact smul_right_injective _ hℓ0 e2

    obtain ⟨kγ, hkγ⟩ := hsat γ
    obtain ⟨kδ, hkδ⟩ := hsat δ
    set k : ℕ := kγ + kδ with hk
    have hγk : ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₂ := by
      have : ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) =
          ((r ^ kδ : ℕ) : ℚ) • (((r ^ kγ : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := by
        rw [smul_smul]; congr 1; rw [hk]; push_cast; ring
      rw [this]; exact hnsmul _ _ hkγ
    have hδk : ((r ^ k : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₂ := by
      have : ((r ^ k : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) =
          ((r ^ kγ : ℕ) : ℚ) • (((r ^ kδ : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) := by
        rw [smul_smul]; congr 1; rw [hk]; push_cast; ring
      rw [this]; exact hnsmul _ _ hkδ
    set xs : ↥R₂ := ⟨((r ^ ms : ℕ) : ℚ) • star ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hms⟩ with hxs
    set xγ : ↥R₂ := ⟨((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hγk⟩ with hxγ
    set xδ : ↥R₂ := ⟨((r ^ k : ℕ) : ℚ) • ((δ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]), hδk⟩ with hxδ
    have hprod : (xs : ℍ[ℚ, a₁, b₁]) * (xγ : ℍ[ℚ, a₁, b₁]) = (xδ : ℍ[ℚ, a₁, b₁]) * (xs : ℍ[ℚ, a₁, b₁]) := by
      simp only [hxs, hxγ, hxδ, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      rw [hkey, mul_comm (((r ^ k : ℕ) : ℚ)) (((r ^ ms : ℕ) : ℚ))]
    have hm1 : (xs : ℍ[ℚ, a₁, b₁]) * (xγ : ℍ[ℚ, a₁, b₁]) ∈ R₂ := hR₂o.mul_mem xs.2 xγ.2
    have hm2 : (xδ : ℍ[ℚ, a₁, b₁]) * (xs : ℍ[ℚ, a₁, b₁]) ∈ R₂ := hR₂o.mul_mem xδ.2 xs.2

    have hstar : ê xγ ≫ ê xs = ê xs ≫ ê xδ := by
      have e3 : (⟨_, hm1⟩ : ↥R₂) = ⟨_, hm2⟩ := Subtype.ext hprod
      rw [← hE5mul xs xγ hm1, e3, hE5mul xδ xs hm2]
    have hcommφ : ê xγ ≫ (as ≫ bs) = (as ≫ bs) ≫ ê xδ := by rw [hH3s]; exact hstar

    have hcop : Nat.Coprime (ℓ.1 : ℕ) (r ^ ks) := Nat.Coprime.pow_right _ hℓr
    have hpresê := StabDictAux.factorsThrough_levK_mapPt_of_comp_eq hΛℤ A₀ A₀s C₀ as has as' has' hCs (r ^ ks) hcop
      bs hbs bs' hbsI (ê xγ) (ê xδ) (hê xγ) (hê xδ) (hE5a xγ).1 (hE5a xδ).1 hcommφ

    obtain ⟨i, j, hij⟩ := hE5d γ xγ k rfl
    obtain ⟨⟨hφ', -, heγ_hom, -⟩, -⟩ := hE1 γ
    intro T t P hP
    have hri : Nat.Coprime (r ^ i) (ℓ.1 : ℕ) := Nat.Coprime.pow_left _ hℓr.symm
    refine StabDictAux.mem_of_nsmulPt_mem_of_coprime A₀.L t (fun Q => FactorsThrough C₀.levK Q) (C₀.levK_one t)
      (fun P Q hP hQ => (C₀.levK_sub t P Q hP hQ).1) _ (ℓ.1 : ℕ) (r ^ i) hℓ1 hri ?_ ?_
    ·
      rw [← StabDictAux.mapPt_nsmulPt A₀.L A₀.L (e γ) (he γ) heγ_hom, C₀.levK_torsion t P hP,
        StabDictAux.mapPt_one A₀.L A₀.L (e γ) (he γ) heγ_hom]
    ·
      rw [← StabDictAux.pushPt_act_natCast A₀ hΛℤ (r ^ i) ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ (by push_cast; rfl) t]
      show FactorsThrough C₀.levK (mapPt (A₀.act _) (A₀.act_over _) (mapPt (e γ) (he γ) P))
      rw [← StabDictAux.mapPt_comp (e γ) (he γ) (A₀.act _) (A₀.act_over _) (by rw [Category.assoc, A₀.act_over, he]),
        StabDictAux.mapPt_congr hij _ (by rw [Category.assoc, A₀.act_over, hê]),
        StabDictAux.mapPt_comp (ê xγ) (hê xγ) (A₀.act _) (A₀.act_over _)]
      exact C₀.levK_stable _ t _ (hpresê t P hP)

end S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_preservesExtraLevel_iff_mem_inf_map_conj_of_heckeDictionary_star_of_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_preservesExtraLevel_iff_mem_inf_map_conj_of_heckeDictionary_star_of_comp_eq (solution)
