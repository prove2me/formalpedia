-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ef9d4955-1fff-5a83-a2bf-4bdde1a57021

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Mathlib.Data.Int.GCD
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace P3Lev

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

end P3Lev

open P3Lev in
theorem solution
    {r N : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (ψ ψ' : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ' E)
    (ub : ρ.Eb.A ⟶ ρ'.Eb.A) (hub : ub ≫ ρ'.gb = ρ.gb) (hub' : ub ≫ ρ'.Eb.f = ρ.Eb.f)
    (θ : A₀.A ⟶ A₀.A) (hθ : ub ≫ ρ'.φ ≫ ρ'.gA = ρ.φ ≫ ρ.gA ≫ θ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓ : IsUnit ((ℓ : ℕ) : B))
    (K₀ : A₀.ExtraLevel ℓ) (m : ℕ) (hm : ¬ ℓ ∣ m)
    (hθK : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})))
        (x : SchemeHomOver t A₀.f),
        (∃ Q₀ : Spec (CommRingCat.of k) ⟶ K₀.K, Q₀ ≫ K₀.levK = x.1 ≫ θ) ↔
          (∃ Q₀ : Spec (CommRingCat.of k) ⟶ K₀.K, Q₀ ≫ K₀.levK = (nsmulPt A₀.L t m x).1))
    (C C' : E.ExtraLevel ℓ)
    (hC : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
      (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA))
    (hC' : (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ'.Eb.f),
      (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ρ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ'.φ) ≫ ρ'.gA)) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
      FactorsThrough C.levK R ↔ FactorsThrough C'.levK R := by
  have hℓb : IsUnit ((ℓ : ℕ) : (B ⧸ Ideal.span {algebraMap 𝒪 B π})) := by
    simpa only [map_natCast] using hℓ.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))

  obtain ⟨hφo, hφ'o, hφmul, hφ'mul, hφlin, hφ'lin, hdeg⟩ := ρ.isIsogenyPair
  obtain ⟨hsq, hmulb, hactb, hlevb⟩ := ρ.isPullback_Eb
  obtain ⟨hsqA, hmulA, hactA, hlevA⟩ := ρ.isPullback_Ab

  have gA_nsmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (n : ℕ) (Q : SchemeHomOver t' ρ.Ab.f),
      (nsmulPt ρ.Ab.L t' n Q).1 ≫ ρ.gA =
        (nsmulPt A₀.L (t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) n
          ⟨Q.1 ≫ ρ.gA, by rw [Category.assoc, hsqA.w, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' n Q
    induction n with
    | zero =>
      show (ρ.Ab.L.one t').1 ≫ ρ.gA = (A₀.L.one _).1
      have h := hmulA t' (ρ.Ab.L.one t') (ρ.Ab.L.one t')
      rw [ρ.Ab.L.one_mul] at h
      have h1 := eq_one_of_mul_self_eq A₀.L (t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)))
        (x := ⟨(ρ.Ab.L.one t').1 ≫ ρ.gA, by rw [Category.assoc, hsqA.w, ← Category.assoc, (ρ.Ab.L.one t').2]⟩)
        (Subtype.ext h.symm)
      exact congrArg Subtype.val h1
    | succ n ih =>
      show (ρ.Ab.L.mul t' (nsmulPt ρ.Ab.L t' n Q) Q).1 ≫ ρ.gA =
        (A₀.L.mul _ (nsmulPt A₀.L _ n ⟨Q.1 ≫ ρ.gA, _⟩) ⟨Q.1 ≫ ρ.gA, _⟩).1
      rw [hmulA]
      have hih : (⟨(nsmulPt ρ.Ab.L t' n Q).1 ≫ ρ.gA, by rw [Category.assoc, hsqA.w, ← Category.assoc, (nsmulPt ρ.Ab.L t' n Q).2]⟩ :
          SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f) =
          nsmulPt A₀.L _ n ⟨Q.1 ≫ ρ.gA, by rw [Category.assoc, hsqA.w, ← Category.assoc, Q.2]⟩ := Subtype.ext ih
      rw [hih]

  obtain ⟨KA, hKA⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ ρ.Ab ρ.gA ρ.isPullback_Ab ℓ K₀

  obtain ⟨KE, hKE, hKEuniq⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
    hΛℤ ρ.Eb ρ.Ab r ρ.d ρ.φ ρ.φ_over ρ.φ' ρ.isIsogenyPair ρ.preservesLevel ℓ hℓr hℓb KA

  obtain ⟨Cb, hCb⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E ρ.Eb ρ.gb ρ.isPullback_Eb ℓ C
  obtain ⟨C'b, hC'b⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia
    (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E ρ.Eb ρ.gb ρ.isPullback_Eb ℓ C'

  have hCbKE : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t' ρ.Eb.f),
      FactorsThrough KE.levK P ↔ FactorsThrough Cb.levK P := by
    apply hKEuniq
    intro T t' P hP
    rw [hKA]
    exact hC t' P ((hCb t' P).1 hP)

  obtain ⟨-, hgeomA⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit ρ.Ab ℓ hℓb KA
  have hC'bKE : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t' ρ.Eb.f),
      FactorsThrough KE.levK P ↔ FactorsThrough C'b.levK P := by
    apply hKEuniq
    intro T t' P hP
    rw [hgeomA]
    refine ⟨?_, ?_⟩
    · rw [← mapPt_nsmulPt ρ.Eb.L ρ.Ab.L ρ.φ ρ.φ_over hφmul, C'b.levK_torsion t' P hP]
      exact eq_one_of_mul_self_eq ρ.Ab.L t' (by rw [← hφmul, ρ.Eb.L.one_mul])
    · intro k _ _ sk τ hτ

      have hPτ : FactorsThrough C'b.levK (schemeHomOverComp τ hτ P) := factorsThrough_comp C'b t' _ τ hτ P hP
      have hmap : schemeHomOverComp τ hτ (mapPt ρ.φ ρ.φ_over P) = mapPt ρ.φ ρ.φ_over (schemeHomOverComp τ hτ P) :=
        Subtype.ext (by simp only [schemeHomOverComp_coe, mapPt_coe, Category.assoc])
      rw [hmap]

      generalize schemeHomOverComp τ hτ P = Pg at hPτ
      clear hmap

      have hℓPg : nsmulPt ρ.Ab.L _ ℓ (mapPt ρ.φ ρ.φ_over Pg) = ρ.Ab.L.one _ := by
        rw [← mapPt_nsmulPt ρ.Eb.L ρ.Ab.L ρ.φ ρ.φ_over hφmul, C'b.levK_torsion _ Pg hPτ]
        exact eq_one_of_mul_self_eq ρ.Ab.L _ (by rw [← hφmul, ρ.Eb.L.one_mul])

      obtain ⟨R₀, hR₀⟩ := (hC'b _ Pg).1 hPτ
      have hR' : ∃ R₀ : Spec (CommRingCat.of k) ⟶ C'.K, R₀ ≫ C'.levK = (Pg.1 ≫ ub) ≫ ρ'.gb :=
        ⟨R₀, by rw [hR₀]; show Pg.1 ≫ ρ.gb = (Pg.1 ≫ ub) ≫ ρ'.gb; rw [Category.assoc, hub]⟩
      obtain ⟨Q₀, hQ₀⟩ := hC' (geomPoint k sk) ⟨Pg.1 ≫ ub, by rw [Category.assoc, hub', Pg.2]⟩ hR'

      have hxo : (Pg.1 ≫ ρ.φ ≫ ρ.gA) ≫ A₀.f = (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) := by
        simp only [Category.assoc]
        rw [hsqA.w, ← Category.assoc ρ.φ, hφo, ← Category.assoc, Pg.2]
      have hθx : ∃ Q₀ : Spec (CommRingCat.of k) ⟶ K₀.K, Q₀ ≫ K₀.levK = (⟨Pg.1 ≫ ρ.φ ≫ ρ.gA, hxo⟩ : SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f).1 ≫ θ :=
        ⟨Q₀, by rw [hQ₀]; simp only [Category.assoc, hθ]⟩
      obtain ⟨Q₁, hQ₁⟩ := (hθK k (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) ⟨Pg.1 ≫ ρ.φ ≫ ρ.gA, hxo⟩).1 hθx

      have hmPg : FactorsThrough KA.levK (mapPt ρ.φ ρ.φ_over (nsmulPt ρ.Eb.L _ m Pg)) := by
        rw [hKA]
        refine ⟨Q₁, ?_⟩
        rw [hQ₁]
        have hpt : (⟨(mapPt ρ.φ ρ.φ_over Pg).1 ≫ ρ.gA, by rw [Category.assoc, hsqA.w, ← Category.assoc, (mapPt ρ.φ ρ.φ_over Pg).2]⟩ :
            SchemeHomOver (geomPoint k sk ≫ Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ))) A₀.f) = ⟨Pg.1 ≫ ρ.φ ≫ ρ.gA, hxo⟩ :=
          Subtype.ext (by simp only [mapPt_coe, Category.assoc])
        show _ = (mapPt ρ.φ ρ.φ_over (nsmulPt ρ.Eb.L _ m Pg)).1 ≫ ρ.gA
        rw [mapPt_nsmulPt ρ.Eb.L ρ.Ab.L ρ.φ ρ.φ_over hφmul, gA_nsmul, hpt]

      have := factorsThrough_of_nsmulPt KA _ m hm (mapPt ρ.φ ρ.φ_over Pg) hℓPg
        (by rw [← mapPt_nsmulPt ρ.Eb.L ρ.Ab.L ρ.φ ρ.φ_over hφmul]; exact hmPg)
      exact this

  have hbb : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t' ρ.Eb.f),
      FactorsThrough Cb.levK P ↔ FactorsThrough C'b.levK P := fun t' P => (hCbKE t' P).symm.trans (hC'bKE t' P)

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

    obtain ⟨P₁, hP₁, hP₂⟩ : ∃ P₁ : Spec (CommRingCat.of k) ⟶ ρ.Eb.A, P₁ ≫ ρ.gb = Rg.1 ∧ P₁ ≫ ρ.Eb.f = geomPoint k sk' :=
      ⟨hsq.lift Rg.1 (geomPoint k sk') (by rw [Rg.2, hgp]), hsq.lift_fst _ _ _, hsq.lift_snd _ _ _⟩
    have e1 : FactorsThrough C.levK Rg ↔ FactorsThrough Cb.levK ⟨P₁, hP₂⟩ := by
      rw [hCb]
      show (∃ P₀, P₀ ≫ C.levK = Rg.1) ↔ (∃ P₀, P₀ ≫ C.levK = P₁ ≫ ρ.gb)
      rw [hP₁]
    have e2 : FactorsThrough C'.levK Rg ↔ FactorsThrough C'b.levK ⟨P₁, hP₂⟩ := by
      rw [hC'b]
      show (∃ P₀, P₀ ≫ C'.levK = Rg.1) ↔ (∃ P₀, P₀ ≫ C'.levK = P₁ ≫ ρ.gb)
      rw [hP₁]
    rw [e1, e2]
    exact hbb _ _
  intro T t R
  rw [hgeomC, hgeomC']
  exact and_congr_right fun _ => forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun sk => forall_congr' fun τ => forall_congr' fun hτ => hgeo k sk _

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_forall_factorsThrough_levK_iff_of_comp_eq_comp_of_forall_geomPoint_iff (solution)
