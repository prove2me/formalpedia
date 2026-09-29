-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.forall_factorsThrough_iff_and_stable_of_isTranslateBy_corr_of_isAlgClosed_heightNormalised_eq_oneLeg_ell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c00d2998-1348-5614-8597-d47499970f8e

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Mathlib.Data.Int.GCD
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_and_stable_of_isTranslateBy_corr_of_isAlgClosed_heightNormalised_eq_oneLeg_ell
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace E188Ell

universe u

section Points

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}

variable (L : GoodReductionJacobian.RelativeGroupLaw R f) (L' : GoodReductionJacobian.RelativeGroupLaw R f')

theorem eq_one_of_mul_self_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x : SchemeHomOver t f}
    (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem nsmulPt_add {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (m + n) P = L.mul t (nsmulPt L t m P) (nsmulPt L t n P) := by
  induction n with
  | zero => show nsmulPt L t m P = L.mul t (nsmulPt L t m P) (L.one t); rw [L.mul_one]
  | succ n ih =>
    show L.mul t (nsmulPt L t (m + n) P) P = L.mul t (nsmulPt L t m P) (L.mul t (nsmulPt L t n P) P)
    rw [ih, L.mul_assoc]

theorem nsmulPt_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (m n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t (m * n) P = nsmulPt L t n (nsmulPt L t m P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show nsmulPt L t (m * n + m) P = L.mul t (nsmulPt L t n (nsmulPt L t m P)) (nsmulPt L t m P)
    rw [nsmulPt_add, ih]

theorem nsmulPt_one_pt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    nsmulPt L t n (L.one t) = L.one t := by
  induction n with
  | zero => rfl
  | succ n ih => show L.mul t (nsmulPt L t n (L.one t)) (L.one t) = L.one t; rw [ih, L.mul_one]

theorem mapPt_nsmulPt (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero =>
    show mapPt φ hφ (L.one t) = L'.one t
    exact eq_one_of_mul_self_eq L' t (by rw [← hhom, L.one_mul])
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hhom, ih]

theorem comp_nsmulPt {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (τ : T' ⟶ T) (hτ : τ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp τ hτ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp τ hτ P) := by
  induction n with
  | zero =>
    show schemeHomOverComp τ hτ (L.one t) = L.one t'
    exact eq_one_of_mul_self_eq L t' (by rw [← L.mul_natural, L.one_mul])
  | succ n ih =>
    show schemeHomOverComp τ hτ (L.mul t (nsmulPt L t n P) P) = L.mul t' (nsmulPt L t' n (schemeHomOverComp τ hτ P)) (schemeHomOverComp τ hτ P)
    rw [L.mul_natural, ih]

end Points

section Level

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
  {E : FakeEllipticCurve Λ N S} {ℓ : ℕ} (K : E.ExtraLevel ℓ)

theorem factorsThrough_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t E.f)
    (hP : FactorsThrough K.levK P) : FactorsThrough K.levK (nsmulPt E.L t n P) := by
  induction n with
  | zero => exact K.levK_one t
  | succ n ih => exact (K.levK_sub t _ _ ih hP).1

theorem factorsThrough_comp {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (τ : T' ⟶ T) (hτ : τ ≫ t = t') (P : SchemeHomOver t E.f) (hP : FactorsThrough K.levK P) :
    FactorsThrough K.levK (schemeHomOverComp τ hτ P) := by
  obtain ⟨P₀, hP₀⟩ := hP
  exact ⟨τ ≫ P₀, by rw [Category.assoc, hP₀]; rfl⟩

theorem factorsThrough_of_nsmulPt [Fact ℓ.Prime] {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (m : ℕ) (hm : ¬ ℓ ∣ m)
    (Q : SchemeHomOver t E.f) (hℓQ : nsmulPt E.L t ℓ Q = E.L.one t) (hmQ : FactorsThrough K.levK (nsmulPt E.L t m Q)) :
    FactorsThrough K.levK Q := by
  have hcop : Nat.Coprime m ℓ := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Fact.out : ℓ.Prime).one_lt
  have hdecomp : m * u = ℓ * (m * u / ℓ) + 1 := by
    have := Nat.div_add_mod (m * u) ℓ
    rw [hu] at this
    exact this.symm
  have key : nsmulPt E.L t (m * u) Q = Q := by
    rw [hdecomp, nsmulPt_add, nsmulPt_mul, hℓQ, nsmulPt_one_pt]
    show E.L.mul t (E.L.one t) (E.L.mul t (E.L.one t) Q) = Q
    rw [E.L.one_mul, E.L.one_mul]
  rw [← key, nsmulPt_mul]
  exact factorsThrough_nsmulPt K t u _ hmQ

end Level

end E188Ell

namespace E188Ell

section ActNat

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem pushPt_act_natCast (E : FakeEllipticCurve Λ N S) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (c : ℕ) (P : SchemeHomOver t E.f) :
    pushPt (E.act ⟨(((c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (E.act_over _) P = nsmulPt E.L t c P := by
  induction c with
  | zero =>
    have h0 : (⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) + ⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
      apply Subtype.ext; push_cast; simp
    have hadd := E.act_add ⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ⟨(((0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ t P
    rw [h0] at hadd
    exact eq_one_of_mul_self_eq E.L t hadd.symm
  | succ c ih =>
    have h1 : (⟨(((c + 1 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨(((c : ℕ) : ℤ) : ℚ), hΛℤ _⟩ + ⟨(((1 : ℤ)) : ℚ), hΛℤ 1⟩ := by
      apply Subtype.ext; push_cast; simp
    have hone : (⟨(((1 : ℤ)) : ℚ), hΛℤ 1⟩ : ↥Λ) = ⟨1, by simpa using hΛℤ 1⟩ := by
      apply Subtype.ext; push_cast; simp
    rw [h1, E.act_add, ih, hone]
    show E.L.mul t (nsmulPt E.L t c P) _ = E.L.mul t (nsmulPt E.L t c P) P
    congr 1
    exact Subtype.ext (by rw [mapPt_coe, E.act_one, Category.comp_id])

end ActNat

end E188Ell

namespace E188Ell

open E188Ell

theorem ell_core
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)
    (ρ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (eγ : A₀.A ⟶ A₀.A) (heγ : eγ ≫ A₀.f = A₀.f)
    (htr : FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ eγ ρ ρ₂)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓ : IsUnit ((ℓ : ℕ) : B))
    (K₀ : A₀.ExtraLevel ℓ)
    (hstab : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
      FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt eγ heγ R))
    (C C' : E.ExtraLevel ℓ)
    (hC : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
      (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA))
    (hC' : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ₂.Eb.f),
      (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ρ₂.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ₂.φ) ≫ ρ₂.gA)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R := by
  have hℓb : IsUnit ((ℓ : ℕ) : (B ⧸ Ideal.span {algebraMap 𝒪 B π})) := by
    simpa only [map_natCast] using hℓ.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))
  have hℓrj : ∀ j : ℕ, ¬ ℓ ∣ r ^ j := fun j h =>
    hℓr ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : r.Prime)).1 ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h))

  obtain ⟨u, uA, ⟨hu_pb, hu_gb, huA_pb, huA_gA⟩, eγb, heγb_gA, heγb_f, i, j, hEQ⟩ := htr
  obtain ⟨hsqu, hmulu, hactu, hlevu⟩ := hu_pb

  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := ρ.isIsogenyPair
  obtain ⟨hsq, hmulb, hactb, hlevb⟩ := ρ.isPullback_Eb
  obtain ⟨hsqA, hmulA, hactA, hlevA⟩ := ρ.isPullback_Ab
  obtain ⟨hφo₂, hφ'o₂, hφmul₂, hφ'mul₂, hφlin₂, hφ'lin₂, hdeg₂⟩ := ρ₂.isIsogenyPair
  obtain ⟨hsq₂, hmulb₂, hactb₂, hlevb₂⟩ := ρ₂.isPullback_Eb
  obtain ⟨hsqA₂, hmulA₂, hactA₂, hlevA₂⟩ := ρ₂.isPullback_Ab

  have gA_nsmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (n : ℕ) (Q : SchemeHomOver t' ρ₂.Ab.f),
      (nsmulPt ρ₂.Ab.L t' n Q).1 ≫ ρ₂.gA =
        (nsmulPt A₀.L (t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) n
          ⟨Q.1 ≫ ρ₂.gA, by rw [Category.assoc, hsqA₂.w, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' n Q
    induction n with
    | zero =>
      show (ρ₂.Ab.L.one t').1 ≫ ρ₂.gA = (A₀.L.one _).1
      have h := hmulA₂ t' (ρ₂.Ab.L.one t') (ρ₂.Ab.L.one t')
      rw [ρ₂.Ab.L.one_mul] at h
      have h1 := eq_one_of_mul_self_eq A₀.L (t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)))
        (x := ⟨(ρ₂.Ab.L.one t').1 ≫ ρ₂.gA, by rw [Category.assoc, hsqA₂.w, ← Category.assoc, (ρ₂.Ab.L.one t').2]⟩)
        (Subtype.ext h.symm)
      exact congrArg Subtype.val h1
    | succ n ih =>
      show (ρ₂.Ab.L.mul t' (nsmulPt ρ₂.Ab.L t' n Q) Q).1 ≫ ρ₂.gA =
        (A₀.L.mul _ (nsmulPt A₀.L _ n ⟨Q.1 ≫ ρ₂.gA, _⟩) ⟨Q.1 ≫ ρ₂.gA, _⟩).1
      rw [hmulA₂]
      have hih : (⟨(nsmulPt ρ₂.Ab.L t' n Q).1 ≫ ρ₂.gA, by rw [Category.assoc, hsqA₂.w, ← Category.assoc, (nsmulPt ρ₂.Ab.L t' n Q).2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f) =
          nsmulPt A₀.L _ n ⟨Q.1 ≫ ρ₂.gA, by rw [Category.assoc, hsqA₂.w, ← Category.assoc, Q.2]⟩ := Subtype.ext ih
      rw [hih]

  obtain ⟨KA, hKA⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ ρ.Ab ρ.gA ρ.isPullback_Ab ℓ K₀
  obtain ⟨KA₂, hKA₂⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ ρ₂.Ab ρ₂.gA ρ₂.isPullback_Ab ℓ K₀

  obtain ⟨KE, hKE, hKEuniq⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
    hΛℤ ρ.Eb ρ.Ab r ρ.d ρ.φ ρ.φ_over ρ.φ' ρ.isIsogenyPair ρ.preservesLevel ℓ hℓr hℓb KA
  obtain ⟨KE₂, hKE₂, hKE₂uniq⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
    hΛℤ ρ₂.Eb ρ₂.Ab r ρ₂.d ρ₂.φ ρ₂.φ_over ρ₂.φ' ρ₂.isIsogenyPair ρ₂.preservesLevel ℓ hℓr hℓb KA₂

  obtain ⟨Cb, hCb⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E ρ.Eb ρ.gb ρ.isPullback_Eb ℓ C
  obtain ⟨C'b, hC'b⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E ρ₂.Eb ρ₂.gb ρ₂.isPullback_Eb ℓ C'
  obtain ⟨KEu, hKEu⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (RingHom.id _) ρ.Eb ρ₂.Eb u ⟨hsqu, hmulu, hactu, hlevu⟩ ℓ KE

  have hCbKE : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t' ρ.Eb.f),
      FactorsThrough KE.levK P ↔ FactorsThrough Cb.levK P := by
    apply hKEuniq
    intro T t' P hP
    rw [hKA]
    exact hC t' P ((hCb t' P).1 hP)

  have hC'bKE₂ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t' ρ₂.Eb.f),
      FactorsThrough KE₂.levK P ↔ FactorsThrough C'b.levK P := by
    apply hKE₂uniq
    intro T t' P hP
    rw [hKA₂]
    exact hC' t' P ((hC'b t' P).1 hP)

  have key : u ≫ ρ.φ ≫ ρ.gA ≫ eγ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρ₂.φ ≫ ρ₂.gA ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    calc u ≫ ρ.φ ≫ ρ.gA ≫ eγ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩
        = u ≫ ρ.φ ≫ (ρ.gA ≫ eγ) ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = u ≫ ρ.φ ≫ (eγb ≫ ρ.gA) ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [heγb_gA]
      _ = u ≫ ρ.φ ≫ eγb ≫ (ρ.gA ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by simp only [Category.assoc]
      _ = u ≫ ρ.φ ≫ eγb ≫ (ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.gA) := by rw [hactA]
      _ = (u ≫ ρ.φ ≫ eγb ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρ.gA := by simp only [Category.assoc]
      _ = (ρ₂.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρ.gA := by rw [hEQ]
      _ = ρ₂.φ ≫ uA ≫ (ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ρ.gA) := by simp only [Category.assoc]
      _ = ρ₂.φ ≫ uA ≫ (ρ.gA ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) := by rw [hactA]
      _ = ρ₂.φ ≫ (uA ≫ ρ.gA) ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp only [Category.assoc]
      _ = ρ₂.φ ≫ ρ₂.gA ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by rw [huA_gA]

  obtain ⟨-, hgeomA₂⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit ρ₂.Ab ℓ hℓb KA₂
  have hKEuKE₂ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t' ρ₂.Eb.f),
      FactorsThrough KE₂.levK P ↔ FactorsThrough KEu.levK P := by
    apply hKE₂uniq
    intro T t' P hP
    rw [hgeomA₂]
    refine ⟨?_, ?_⟩
    · rw [← mapPt_nsmulPt ρ₂.Eb.L ρ₂.Ab.L ρ₂.φ ρ₂.φ_over hφmul₂, KEu.levK_torsion t' P hP]
      exact eq_one_of_mul_self_eq ρ₂.Ab.L t' (by rw [← hφmul₂, ρ₂.Eb.L.one_mul])
    · intro k _ _ sk τ hτ
      have hPτ : FactorsThrough KEu.levK (schemeHomOverComp τ hτ P) := factorsThrough_comp KEu t' _ τ hτ P hP
      have hmap : schemeHomOverComp τ hτ (mapPt ρ₂.φ ρ₂.φ_over P) = mapPt ρ₂.φ ρ₂.φ_over (schemeHomOverComp τ hτ P) :=
        Subtype.ext (by simp only [schemeHomOverComp_coe, mapPt_coe, Category.assoc])
      rw [hmap]
      generalize schemeHomOverComp τ hτ P = Pg at hPτ
      clear hmap

      have hℓPg : nsmulPt ρ₂.Ab.L _ ℓ (mapPt ρ₂.φ ρ₂.φ_over Pg) = ρ₂.Ab.L.one _ := by
        rw [← mapPt_nsmulPt ρ₂.Eb.L ρ₂.Ab.L ρ₂.φ ρ₂.φ_over hφmul₂, KEu.levK_torsion _ Pg hPτ]
        exact eq_one_of_mul_self_eq ρ₂.Ab.L _ (by rw [← hφmul₂, ρ₂.Eb.L.one_mul])
      have hyo : (Pg.1 ≫ ρ₂.φ ≫ ρ₂.gA) ≫ A₀.f = (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) := by
        simp only [Category.assoc]
        rw [hsqA₂.w, ← Category.assoc ρ₂.φ, hφo₂, ← Category.assoc, Pg.2]
      let y : SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f :=
        ⟨Pg.1 ≫ ρ₂.φ ≫ ρ₂.gA, hyo⟩
      have hypt : (⟨(mapPt ρ₂.φ ρ₂.φ_over Pg).1 ≫ ρ₂.gA, by rw [Category.assoc, hsqA₂.w, ← Category.assoc, (mapPt ρ₂.φ ρ₂.φ_over Pg).2]⟩ :
            SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f) = y :=
        Subtype.ext (by simp only [mapPt_coe, Category.assoc]; rfl)
      have hℓy : nsmulPt A₀.L _ ℓ y = A₀.L.one _ := by
        apply Subtype.ext
        rw [← hypt, ← gA_nsmul, hℓPg]
        exact (gA_nsmul _ 0 (mapPt ρ₂.φ ρ₂.φ_over Pg))

      have hPu : FactorsThrough KE.levK (t := (geomPoint k sk) ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)))
          ⟨Pg.1 ≫ u, by rw [Category.assoc, hsqu.w, ← Category.assoc, Pg.2]⟩ := (hKEu _ Pg).1 hPτ
      have hPuφ := hKE _ _ hPu
      rw [hKA] at hPuφ

      obtain ⟨Q₀, hQ₀⟩ := hPuφ
      have hid : Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) = 𝟙 _ := by
        rw [CommRingCat.ofHom_id]; exact Spec.map_id _
      have hxo : (Pg.1 ≫ u ≫ ρ.φ ≫ ρ.gA) ≫ A₀.f = (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) := by
        simp only [Category.assoc]
        rw [hsqA.w, ← Category.assoc ρ.φ, hφo, ← Category.assoc u, hsqu.w, hid, Category.comp_id, ← Category.assoc, Pg.2]
      let x : SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f :=
        ⟨Pg.1 ≫ u ≫ ρ.φ ≫ ρ.gA, hxo⟩
      have hxK : FactorsThrough K₀.levK x := by
        refine ⟨Q₀, ?_⟩
        rw [hQ₀]
        show _ = Pg.1 ≫ u ≫ ρ.φ ≫ ρ.gA
        simp only [mapPt_coe, Category.assoc]
      have hxK' := K₀.levK_stable ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ _ _ (hstab _ x hxK)

      have hval : (pushPt (A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _) (mapPt eγ heγ x)).1 =
          (pushPt (A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (A₀.act_over _) y).1 := by
        simp only [mapPt_coe]
        show (Pg.1 ≫ u ≫ ρ.φ ≫ ρ.gA) ≫ eγ ≫ A₀.act _ = (Pg.1 ≫ ρ₂.φ ≫ ρ₂.gA) ≫ A₀.act _
        simp only [Category.assoc]
        rw [← Category.assoc u, ← Category.assoc (u ≫ ρ.φ), ← Category.assoc ((u ≫ ρ.φ) ≫ ρ.gA)]
        simp only [Category.assoc] at key ⊢
        rw [key]
      have hjy : FactorsThrough K₀.levK (nsmulPt A₀.L _ (r ^ j) y) := by
        rw [← pushPt_act_natCast A₀ hΛℤ _ (r ^ j) y]
        obtain ⟨Q₁, hQ₁⟩ := hxK'
        exact ⟨Q₁, by rw [hQ₁, hval]⟩
      have hyK : FactorsThrough K₀.levK y := factorsThrough_of_nsmulPt K₀ _ (r ^ j) (hℓrj j) y hℓy hjy

      rw [hKA₂, hypt]
      exact hyK

  obtain ⟨-, hgeomC⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit E ℓ hℓ C
  obtain ⟨-, hgeomC'⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit E ℓ hℓ C'
  have hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k) (Rg : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough C.levK Rg ↔ FactorsThrough C'.levK Rg := by
    intro k _ _ sk Rg
    have hπ0 : sk (algebraMap 𝒪 B π) = 0 := (hBπ.map sk).eq_zero
    have hI : ∀ x ∈ Ideal.span {algebraMap 𝒪 B π}, sk x = 0 := fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [map_mul, hπ0, mul_zero]
    let sk' : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* k := Ideal.Quotient.lift _ sk hI
    have hsk : sk'.comp (Ideal.Quotient.mk _) = sk := Ideal.Quotient.lift_comp_mk _ sk hI
    have hgp : geomPoint k sk = geomPoint k sk' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) := by
      simp only [geomPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsk]

    obtain ⟨P₁, hP₁, hP₂⟩ : ∃ P₁ : Spec (CommRingCat.of k) ⟶ ρ₂.Eb.A, P₁ ≫ ρ₂.gb = Rg.1 ∧ P₁ ≫ ρ₂.Eb.f = geomPoint k sk' :=
      ⟨hsq₂.lift Rg.1 (geomPoint k sk') (by rw [Rg.2, hgp]), hsq₂.lift_fst _ _ _, hsq₂.lift_snd _ _ _⟩
    have e1 : FactorsThrough C.levK Rg ↔ FactorsThrough Cb.levK (t := geomPoint k sk' ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)))
        ⟨P₁ ≫ u, by rw [Category.assoc, hsqu.w, ← Category.assoc, hP₂]⟩ := by
      rw [hCb]
      show (∃ P₀, P₀ ≫ C.levK = Rg.1) ↔ (∃ P₀, P₀ ≫ C.levK = (P₁ ≫ u) ≫ ρ.gb)
      rw [Category.assoc, hu_gb, hP₁]
    have e2 : FactorsThrough C'.levK Rg ↔ FactorsThrough C'b.levK ⟨P₁, hP₂⟩ := by
      rw [hC'b]
      show (∃ P₀, P₀ ≫ C'.levK = Rg.1) ↔ (∃ P₀, P₀ ≫ C'.levK = P₁ ≫ ρ₂.gb)
      rw [hP₁]
    rw [e1, e2, ← hCbKE, ← hC'bKE₂, hKEuKE₂, hKEu]
  intro T t R
  rw [hgeomC, hgeomC']
  exact and_congr_right fun _ => forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun sk => forall_congr' fun τ => forall_congr' fun hτ => hgeo k sk _

end E188Ell

open IsDedekindDomain CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

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
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

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

        (hE5b1 : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
        (hE5b2 : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
            ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
        (hE5b3 : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

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

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (MD : ModuliPackage.{0, 0} r Onr) (hMD : MD.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → MD.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = MD.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : MD.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  MD.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

      (eD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 MD).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)

      (hnatD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 MD).obj B), eD B' hB' ((ModuliPackage.G 𝒪 MD).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (eD B hB x))

      (hbijD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (eD B hB))

      (hfstD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 MD).obj B), (eD B hB x).1 = x.ψ)

      (hGLD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (eD B hB x) (eD B hB x'))

      (hPiD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → eD B hB x' = (frobTwist Onr Fr 1 (eD B hB x).1, (eD B hB x).2))

      (hPiexD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 MD).obj B), ∃ x' : (ModuliPackage.G 𝒪 MD).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x')

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (P₀ : A₀.FullLevel n)

    (A₀w : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (kw : ℕ) (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f) (bw' : A₀.A ⟶ A₀w.A) (habw : (aw ≫ bw) ≫ A₀.f = A₀.f)
    (hALw : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (hBSw : FakeEllipticCurve.IsIsogenyPair (r ^ kw) A₀w A₀ bw bw') (hBSwlev : FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw)
    (hJOINTw :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧

          (∃ (εw : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k_w : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ v : Fin 2 → B', (∀ i, v i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εw : MvFormalGroup.End X₀.F).toPowerSeries i) v) =
                  mapPt (aw ≫ bw) habw (θ₀ B' v)) ∧
              E₀ εw = ((r : K₀) ^ k_w) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((wbar : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 MD B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (g₀ : Matrix.GeneralLinearGroup (Fin 2) K₀)

      (heqΓ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (E : FakeEllipticCurve Λ N B) (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) (γ : ↥Γt),
          FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e γ) ρ ρ' →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ : (ℍ[ℚ, a₁, b₁])ˣ) * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨E, ρ'⟩))

      (heqW : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hrbarB : IsUnit ((rbar : ℕ) : B))
          (E Ef : FakeEllipticCurve Λ N B)
          (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f) (q' : Ef.A ⟶ E.A) (hq' : q' ≫ E.f = Ef.f),
          FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar E Ef q hq q' hq' →
          ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef),
          (∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
            (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
            (ewb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : ewb ≫ ρ.gA = ρ.gA ≫ (aw ≫ bw)) (_ : ewb ≫ ρ.Ab.f = ρ.Ab.f)
            (i j : ℕ),
            qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ewb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) wbar * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨Ef, ρf⟩))

      (hK1 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
          ∃ (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
            (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧
            OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P))

      (hK2 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (E' : FakeEllipticCurve Λ N B) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E'),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E', ϱ'⟩)) (ψ, P) →
            ∃ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), FakeEllipticCurve.IsoVia E E' i hi ∧
              (∃ (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
                (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ.gA = ϱ'.gA)
                (i₁ j₁ : ℕ),
                ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

      (hK3 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
          (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
            ∃ (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
              (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) E'),
              FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ϱ ϱ' ∧
              (Ξ B' (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) hB' ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) ∧ OmegaNr.IsTwistedAct π Onr Fr vdet B' g₀⁻¹ (eD B' hB' (Ξ B' (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (φ.comp ψ)) hB' ⟨E', ϱ'⟩)) ((φ.comp ψ), ((Omega K₀ π).map φ P)))

      (hK4 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [IsNoetherianRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
            (hg : FakeEllipticCurve.IsPullbackVia (p : B →+* B₀) E E₀ g) (ϱ₀ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) E₀),
            (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) →
            ∃ (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (ϱ₀' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) E₀),
              FakeEllipticCurve.Rigidification.IsPullbackVia p g hg ϱ ϱ₀' ∧ (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧
              ∀ P₀' : (Omega K₀ π).obj B₀,
                OmegaNr.IsTwistedAct π Onr Fr vdet B₀ g₀⁻¹ (eD B₀ hB₀ (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀⟩)) ((p.comp ψ), P₀') ↔
                  OmegaNr.IsTwistedAct π Onr Fr vdet B₀ g₀⁻¹ (eD B₀ hB₀ (Ξ B₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) (p.comp ψ)) hB₀ ⟨E₀, ϱ₀'⟩)) ((p.comp ψ), P₀'))

      (hC0e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E)
          (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2), E.IsFormalModuleVia coord X θ →
          ∃ Pn : E.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn)

      (hC0u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (Pn Pn' : E.FullLevel n),
          FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn' → Pn.P = Pn'.P)

      (Θf : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)

      (hnat : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))

      (hG : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g))

      (hC2 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (Pn : E.FullLevel n),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn →
            (Θf B hB ((ψ, P), (1 : G))).1 = (ptF B (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) ⟨E, Pn⟩).1)

    (hC2c : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B)
          (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
            (Θf B hB ((ψ, P), (1 : G))).1 ≫ p = (pt B (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) E).1)

    (θt : ↥Γt →* G)

    (hC3 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E),
          (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) → OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hB ⟨E, ϱ⟩)) (ψ, P) →
          ∀ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (ψ' : Onr →ₐ[𝒪] B) (P' : (Omega K₀ π).obj B),
            OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) (ψ, P) (ψ', P') →
            ∃ ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') E,
              (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') hB ⟨E, ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') ∧ OmegaNr.IsTwistedAct π Onr Fr vdet B g₀⁻¹ (eD B hB (Ξ B (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ') hB ⟨E, ϱ'⟩)) (ψ', P') ∧
              (∀ (Pn Pn' : E.FullLevel n), FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ' Pn' →
                  Pn'.P = pushPt (E.act (χ (θt ⟨γ, hγ⟩))) (E.act_over (χ (θt ⟨γ, hγ⟩))) Pn.P) ∧
              (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ),
                  (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
                      FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt (e ⟨γ, hγ⟩) (he ⟨γ, hγ⟩) R)) →
                  ∀ (C C' : E.ExtraLevel ℓ), (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) → (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ'.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ϱ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ'.φ) ≫ ϱ'.gA) →
                    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
                      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π))
    (ψ : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k)
    (E : FakeEllipticCurve Λ N k) (ϱ : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E) (E' : FakeEllipticCurve Λ N k) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E')
    (hΞψ : (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ)) (hev : OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ⟩)) (ψ, P))
    (hΞψ' : (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ)) (hev' : OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E', ϱ'⟩)) (ψ, P'))
    (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hvia : FakeEllipticCurve.IsoVia E E' i hi)

    (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
    (ϱ'' : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E)
    (hev'' : (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ''⟩).ψ = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) ∧ OmegaNr.IsTwistedAct π Onr Fr vdet k g₀⁻¹ (eD k hk (Ξ k (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) hk ⟨E, ϱ''⟩)) (ψ, P'))
    (htw : OmegaNr.IsTwistedAct π Onr Fr vdet k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) (ψ, P) (ψ, P'))
    (htr : FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e ⟨γ, hγ⟩) ϱ ϱ'')
    (hcorr : (∃ (ib : ϱ''.Eb.A ⟶ ϱ'.Eb.A) (_ : ib ≫ ϱ'.gb = ϱ''.gb ≫ i.hom) (_ : ib ≫ ϱ'.Eb.f = ϱ''.Eb.f)
                (uA : ϱ'.Ab.A ⟶ ϱ''.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ''.Ab ϱ'.Ab uA) (_ : uA ≫ ϱ''.gA = ϱ'.gA)
                (i₁ j₁ : ℕ),
                ib ≫ ϱ'.φ ≫ uA ≫ ϱ''.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ''.φ ≫ ϱ''.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    :
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : k) → ∀ (K₀ : A₀.ExtraLevel ℓ),
                  (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (R : SchemeHomOver t A₀.f),
                      FactorsThrough K₀.levK R → FactorsThrough K₀.levK (mapPt (e ⟨γ, hγ⟩) (he ⟨γ, hγ⟩) R)) →
                  ∀ (C C' : E.ExtraLevel ℓ), (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (R : SchemeHomOver t' ϱ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) → (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) (R : SchemeHomOver t' ϱ''.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ϱ''.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ''.φ) ≫ ϱ''.gA) →
                    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (R : SchemeHomOver t E.f),
                      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R) := by
  intro ℓ' _ hℓr' hℓk' K₀' hst' C₁ C₂ hC₁ hC₂
  exact E188Ell.ell_core 𝒪 π Onr Λ hΛℤ A₀ k hk (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ) E ϱ ϱ'' (e ⟨γ, hγ⟩) (he ⟨γ, hγ⟩)
    htr ℓ' hℓr' hℓk' K₀' hst' C₁ C₂ hC₁ hC₂

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_and_stable_of_isTranslateBy_corr_of_isAlgClosed_heightNormalised_eq_oneLeg_ell
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_iff_and_stable_of_isTranslateBy_corr_of_isAlgClosed_heightNormalised_eq_oneLeg_ell (solution)
