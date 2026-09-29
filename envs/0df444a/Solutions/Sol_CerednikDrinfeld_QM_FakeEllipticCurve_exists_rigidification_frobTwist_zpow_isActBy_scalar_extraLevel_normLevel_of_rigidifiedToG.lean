-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidification_frobTwist_zpow_isActBy_scalar_extraLevel_normLevel_of_rigidifiedToG
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7db76ff8-edfb-5020-9061-3e5860a418bf

import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_frobTwist_isActBy_scalar_levelCompat_heightNormalised_of_rigidifiedToG
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_transport_and_eq_of_rigidification_normLevelTransport
import Theorems.Thm_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
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
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_frobTwist_zpow_isActBy_scalar_extraLevel_normLevel_of_rigidifiedToG
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

open CategoryTheory.Limits

namespace TCLTransport

open CerednikDrinfeld.QM.FakeEllipticCurve

section Generic

variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem ft_comp {A C : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (lev : C ⟶ A)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} {t' : T' ⟶ Spec (CommRingCat.of S)}
    (τ : T' ⟶ T) (hτ : τ ≫ t = t') (P : SchemeHomOver t f) :
    FactorsThrough lev P → FactorsThrough lev (schemeHomOverComp τ hτ P) := by
  rintro ⟨P₀, hP₀⟩
  exact ⟨τ ≫ P₀, by rw [Category.assoc, hP₀]; rfl⟩

theorem ft_of_ft_of_forall_imp (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : S))
    (K K' : E.ExtraLevel ℓ)
    (hKK' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P → FactorsThrough K'.levK P)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough K'.levK P → FactorsThrough K.levK P := by
  classical
  intro hP
  obtain ⟨-, hEt⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit E ℓ hℓ K
  refine (hEt t P).2 ⟨K'.levK_torsion t P hP, ?_⟩
  intro k _ _ sk τ hτ
  have hℓk : (ℓ : k) ≠ 0 := by
    have := hℓ.map sk; rw [map_natCast] at this; exact this.ne_zero
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨eK, -⟩ := K.levK_fibre k sk hℓk
  obtain ⟨eK', -⟩ := K'.levK_fibre k sk hℓk
  let SK := {Q : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough K.levK Q}
  let SK' := {Q : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough K'.levK Q}
  haveI : Finite SK' := Finite.of_equiv _ eK'
  let F : SK → SK' := fun x => ⟨x.1, hKK' _ x.1 x.2⟩
  have hcard : Nat.card SK = Nat.card SK' := by rw [← Nat.card_congr eK, ← Nat.card_congr eK']
  have Finj : Function.Injective F := by
    intro x y hxy
    have h0 := congrArg Subtype.val hxy
    exact Subtype.ext h0
  have hbij := (Nat.bijective_iff_injective_and_card F).2 ⟨Finj, hcard⟩
  obtain ⟨x, hx⟩ := hbij.2 ⟨schemeHomOverComp τ hτ P, ft_comp K'.levK τ hτ P hP⟩
  have hx1 : x.1 = schemeHomOverComp τ hτ P := congrArg Subtype.val hx
  rw [← hx1]
  exact x.2

end Generic

section Rig

variable {r N : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
  {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B)

theorem key (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓB : IsUnit ((ℓ : ℕ) : B)) (K₀ : A₀.ExtraLevel ℓ) :
    ∃ Kb : ϱ.Eb.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
          FactorsThrough Kb.levK R → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) ∧
      ∀ C : E.ExtraLevel ℓ,
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
            (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA) →
        ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
          FactorsThrough Kb.levK R ↔ ∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb := by
  have hℓb : IsUnit ((ℓ : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}) := by
    have := hℓB.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})); rwa [map_natCast] at this
  obtain ⟨KA, hKA⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia _ A₀ ϱ.Ab ϱ.gA
      ϱ.isPullback_Ab ℓ K₀
  obtain ⟨Kb, hKb, hKbu⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_imp_of_isIsogenyPair_pow_of_ne_of_intCast_mem
      hΛℤ ϱ.Eb ϱ.Ab r ϱ.d ϱ.φ ϱ.φ_over ϱ.φ' ϱ.isIsogenyPair ϱ.preservesLevel ℓ hℓr hℓb KA
  refine ⟨Kb, fun t' R hR => (hKA t' (mapPt ϱ.φ ϱ.φ_over R)).1 (hKb t' R hR), fun C hC T t' R => ?_⟩
  obtain ⟨Cb, hCb⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia _ E ϱ.Eb ϱ.gb
      ϱ.isPullback_Eb ℓ C
  have hCbA : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (P : SchemeHomOver t ϱ.Eb.f),
      FactorsThrough Cb.levK P → FactorsThrough KA.levK (mapPt ϱ.φ ϱ.φ_over P) := fun t P hP =>
    (hKA t (mapPt ϱ.φ ϱ.φ_over P)).2 (hC t P ((hCb t P).1 hP))
  rw [hKbu Cb hCbA t' R]
  exact hCb t' R

theorem exists_C (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hB : IsNilpotent (algebraMap 𝒪 B π)) (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓr : ℓ ≠ r) (hℓB : IsUnit ((ℓ : ℕ) : B)) (K₀ : A₀.ExtraLevel ℓ) :
    ∃ C : E.ExtraLevel ℓ, ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ϱ.Eb.f),
      (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ϱ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ϱ.φ) ≫ ϱ.gA := by
  obtain ⟨Kb, hKb, -⟩ := key π A₀ ψ E hΛℤ ϱ ℓ hℓr hℓB K₀
  have hℓb : IsUnit ((ℓ : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}) := by
    have := hℓB.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})); rwa [map_natCast] at this
  obtain ⟨hgb, mgb, agb, lgb⟩ := ϱ.isPullback_Eb
  have hI : IsNilpotent (RingHom.ker (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) := by
    obtain ⟨m, hm⟩ := hB
    refine ⟨m, ?_⟩
    rw [Ideal.mk_ker, Ideal.span_singleton_pow, hm]
    simp
  obtain ⟨C, hC⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker E ϱ.Eb ℓ hℓB
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) Ideal.Quotient.mk_surjective hI ϱ.gb hgb mgb agb lgb Kb
  obtain ⟨Cb, hCb⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia _ E ϱ.Eb ϱ.gb
      ϱ.isPullback_Eb ℓ C
  refine ⟨C, fun t' R hR => hKb t' R ?_⟩
  exact ft_of_ft_of_forall_imp ϱ.Eb ℓ hℓb Kb Cb (fun t P hP => (hCb t P).2 (hC t P hP)) t' R ((hCb t' R).2 hR)

end Rig

end TCLTransport

namespace F530

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

theorem frobTwist_frobTwist {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (frobTwist Onr Fr b ψ) = frobTwist Onr Fr (b + a) ψ := by
  apply AlgHom.ext
  intro x
  simp [frobTwist, AlgHom.comp_apply, zpow_add, AlgEquiv.mul_apply]

theorem frobTwist_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr 0 ψ = ψ := by
  apply AlgHom.ext
  intro x
  simp [frobTwist]

theorem frobTwist_comm {B : Type} [CommRing B] [Algebra 𝒪 B] (a b : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (frobTwist Onr Fr b ψ) = frobTwist Onr Fr b (frobTwist Onr Fr a ψ) := by
  rw [frobTwist_frobTwist, frobTwist_frobTwist, add_comm]

theorem frobTwist_comp {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
    (a : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr a (φ.comp ψ) = φ.comp (frobTwist Onr Fr a ψ) := by
  apply AlgHom.ext
  intro x
  simp [frobTwist]

end F530

namespace F530N

theorem eq_of_pow_eq_pow_of_coprime {G : Type*} [Group G] (n k : ℕ) (hk : Nat.Coprime k n) (u w : G)
    (hu : u ^ n = 1) (hw : w ^ n = 1) (h : u ^ k = w ^ k) : u = w := by
  have hg : (1 : ℤ) = (k : ℤ) * Nat.gcdA k n + (n : ℤ) * Nat.gcdB k n := by
    have := Nat.gcd_eq_gcd_ab k n
    rw [Nat.Coprime.gcd_eq_one hk] at this
    exact_mod_cast this
  have key : ∀ v : G, v ^ n = 1 → v = (v ^ k) ^ (Nat.gcdA k n) := by
    intro v hv
    conv_lhs => rw [← zpow_one v, hg]
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hv, one_zpow, mul_one]
  rw [key u hu, key w hw, h]

theorem chain_pow {G : Type*} [Group G] (r n : ℕ) (hrn : Nat.Coprime r n) (x y z : G)
    (hx : x ^ n = 1) (hz : z ^ n = 1) (A B : ℤ)
    (h1 : y ^ (r ^ A.toNat) = x ^ (r ^ (-A).toNat)) (h2 : z ^ (r ^ B.toNat) = y ^ (r ^ (-B).toNat)) :
    z ^ (r ^ (A + B).toNat) = x ^ (r ^ (-(A + B)).toNat) := by
  have hm1 : A.toNat + B.toNat = (A + B).toNat + (A.toNat + B.toNat - (A + B).toNat) := by omega
  have hm2 : (-A).toNat + (-B).toNat = (-(A + B)).toNat + (A.toNat + B.toNat - (A + B).toNat) := by omega
  have key : z ^ (r ^ (A.toNat + B.toNat)) = x ^ (r ^ ((-A).toNat + (-B).toNat)) := by
    calc z ^ (r ^ (A.toNat + B.toNat)) = (z ^ (r ^ B.toNat)) ^ (r ^ A.toNat) := by rw [pow_add, mul_comm, pow_mul]
      _ = (y ^ (r ^ (-B).toNat)) ^ (r ^ A.toNat) := by rw [h2]
      _ = (y ^ (r ^ A.toNat)) ^ (r ^ (-B).toNat) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (x ^ (r ^ (-A).toNat)) ^ (r ^ (-B).toNat) := by rw [h1]
      _ = x ^ (r ^ ((-A).toNat + (-B).toNat)) := by rw [← pow_mul, ← pow_add]
  rw [hm1, hm2, pow_add, pow_add, pow_mul, pow_mul] at key
  refine eq_of_pow_eq_pow_of_coprime n _ (Nat.Coprime.pow_left _ hrn) _ _ ?_ ?_ key
  · rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
  · rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

theorem nsmulPt_eq_pow {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t m P = (letI := L.pointGroup t; P ^ m) := by
  letI := L.pointGroup t
  induction m with
  | zero => show L.one t = P ^ 0; rw [pow_zero]; rfl
  | succ m ih => show L.mul t (nsmulPt L t m P) P = P ^ (m + 1); rw [ih, pow_succ]; rfl

theorem nsmulPt_chain {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (r n : ℕ) (hrn : Nat.Coprime r n)
    (x y z : SchemeHomOver t f) (hx : nsmulPt L t n x = L.one t) (hz : nsmulPt L t n z = L.one t) (A B : ℤ)
    (h1 : nsmulPt L t (r ^ A.toNat) y = nsmulPt L t (r ^ (-A).toNat) x)
    (h2 : nsmulPt L t (r ^ B.toNat) z = nsmulPt L t (r ^ (-B).toNat) y) :
    nsmulPt L t (r ^ (A + B).toNat) z = nsmulPt L t (r ^ (-(A + B)).toNat) x := by
  letI := L.pointGroup t
  simp only [nsmulPt_eq_pow] at hx hz h1 h2 ⊢
  exact chain_pow r n hrn x y z hx hz A B h1 h2

end F530N

open F530 in
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
    :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
      (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
      (k : ℤ) (ψ' : Onr →ₐ[𝒪] B), ψ' = frobTwist Onr Fr k ψ →
      ∃ (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ' E) (c : ℤ),
        ModuliPackage.G.IsActBy ι Φ η Fr E₀ ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c)
          (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ' hB ⟨E, ρ'⟩) ∧

        (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ) (C C' : E.ExtraLevel ℓ),
                    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA) → (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ'.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ρ'.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ'.φ) ≫ ρ'.gA) →
                      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
                        FactorsThrough C.levK R ↔ FactorsThrough C'.levK R) ∧ (∀ (Pn Pn' : E.FullLevel n), FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn → FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ' Pn' → nsmulPt E.L (𝟙 _) (r ^ c.toNat) Pn'.P = nsmulPt E.L (𝟙 _) (r ^ (-c).toNat) Pn.P) := by
  classical
  obtain ⟨Luniq, Lex, Lone, Lmul, -, -, -, -⟩ :=
    CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws π Onr Fr vdet (K₀ := K₀)
  set Z : Matrix.GeneralLinearGroup (Fin 2) K₀ := (Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) with hZdef
  have hXR : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
        (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E),
        (∃ (ρp : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (1) ψ) E) (c : ℤ),
            ModuliPackage.G.IsActBy ι Φ η Fr E₀ (Z ^ c)
              (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B (frobTwist Onr Fr (1) ψ) hB ⟨E, ρp⟩) ∧
            (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ) (C C' : E.ExtraLevel ℓ),
                (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA) →
                (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρp.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ρp.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρp.φ) ≫ ρp.gA) →
                ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
                  FactorsThrough C.levK R ↔ FactorsThrough C'.levK R) ∧
            (∀ (n : ℕ), IsUnit ((n : ℕ) : B) → ∀ (P₀ : A₀.FullLevel n) (Pn Pn' : E.FullLevel n),
                FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn →
                FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρp Pn' →
                nsmulPt E.L (𝟙 _) (r ^ c.toNat) Pn'.P = nsmulPt E.L (𝟙 _) (r ^ (-c).toNat) Pn.P)) ∧
        (∃ (ρm : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (-1) ψ) E) (c : ℤ),
            ModuliPackage.G.IsActBy ι Φ η Fr E₀ (Z ^ c)
              (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B (frobTwist Onr Fr (-1) ψ) hB ⟨E, ρm⟩) ∧
            (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ) (C C' : E.ExtraLevel ℓ),
                (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
                  (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA) →
                (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρm.Eb.f),
                  (∃ R₀ : T ⟶ C'.K, R₀ ≫ C'.levK = R.1 ≫ ρm.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρm.φ) ≫ ρm.gA) →
                ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (R : SchemeHomOver t E.f),
                  FactorsThrough C.levK R ↔ FactorsThrough C'.levK R) ∧
            (∀ (n : ℕ), IsUnit ((n : ℕ) : B) → ∀ (P₀ : A₀.FullLevel n) (Pn Pn' : E.FullLevel n),
                FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn →
                FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρm Pn' →
                nsmulPt E.L (𝟙 _) (r ^ c.toNat) Pn'.P = nsmulPt E.L (𝟙 _) (r ^ (-c).toNat) Pn.P)) := by
    exact CerednikDrinfeld.QM.FakeEllipticCurve.exists_rigidification_frobTwist_isActBy_scalar_levelCompat_heightNormalised_of_rigidifiedToG
      (r := r) (rbar := rbar) (N := N) (hrr := hrr) (hrN := hrN) (𝒪 := 𝒪) (hdvr := hdvr) (π := π) (hπ := hπ) (hcomplete := hcomplete) (hres := hres) (hunr := hunr) (K₀ := K₀) (Onr := Onr) (Fr := Fr) (hOnr_complete := hOnr_complete) (hOnr_max := hOnr_max) (hOnr_alg := hOnr_alg) (hOnr_closed := hOnr_closed) (hFr := hFr) (a := a) (b := b) (hB := hB) (Λ := Λ) (hΛ := hΛ) (hΛℤ := hΛℤ) (coord := coord) (hcoord := hcoord) (A₀ := A₀) (X₀ := X₀) (hX₀ := hX₀) (θ₀ := θ₀) (hA₀ := hA₀) (ι := ι) (Φ := Φ) (hΦ := hΦ) (hΦ4 := hΦ4) (M := MD) (hM := hMD) (η := η) (hη := hη) (E₀ := E₀) (hE₀ := hE₀) (κ := κ) (hκ := hκ) (n₀ := n₀) (β₀ := β₀) (hβ₀ := hβ₀) (Ξ := Ξ) (hΞleg := hΞleg) (hΞnat := hΞnat) (hΞiso := hΞiso) (hΞdef := hΞdef)
  obtain ⟨hC0e, hC0u⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_transport_and_eq_of_rigidification_normLevelTransport
      (r := r) (rbar := rbar) (N := N) (hrr := hrr) (hrN := hrN) (hrbarN := hrbarN) (hN := hN) (𝒪 := 𝒪) (hdvr := hdvr) (π := π) (hπ := hπ) (hcomplete := hcomplete) (hres := hres) (hunr := hunr) (K₀ := K₀) (Onr := Onr) (Fr := Fr) (hOnr_complete := hOnr_complete) (hOnr_max := hOnr_max) (hOnr_alg := hOnr_alg) (hOnr_closed := hOnr_closed) (hFr := hFr) (vdet := vdet) (hvdet := hvdet) (a := a) (b := b) (hB := hB) (Λ := Λ) (hΛ := hΛ) (𝒳 := 𝒳) (f := f) (pt := pt) (h𝒳 := h𝒳) (n := n) (hn := hn) (hrn := hrn) (hrbarn := hrbarn) (hnN := hnN) (M := M) (fM := fM) (ptF := ptF) (hM := hM) (G := G) (ρ := ρ) (χ := χ) (hρ := hρ) (p := p) (hp := hp) (hρp := hρp) (hp_pt := hp_pt) (𝒴 := 𝒴) (g := g) (ptT := ptT) (h𝒴 := h𝒴) (d₀ := d₀) (d₁ := d₁) (hd₀f := hd₀f) (hd₁f := hd₁f) (hd₀ := hd₀) (hd₁ := hd₁) (ar := ar) (arbar := arbar) (harf := harf) (harbarf := harbarf) (har := har) (harbar := harbar) (a₁ := a₁) (b₁ := b₁) (hdef := hdef) (Λ₁ := Λ₁) (R₁ := R₁) (hΛ₁ := hΛ₁) (hR₁ := hR₁) (hRΛ₁ := hRΛ₁) (n₁ := n₁) (hn₁ := hn₁) (hS₁ := hS₁) (ι₀ := ι₀) (hι₀ := hι₀) (v := v) (hv := hv) (Γt := Γt) (hΓt := hΓt) (s := s) (sf := sf) (hs := hs) (Γtℓ := Γtℓ) (hΓtℓ := hΓtℓ) (wbar := wbar) (hwbar := hwbar) (hΛℤ := hΛℤ) (coord := coord) (hcoord := hcoord) (A₀ := A₀) (X₀ := X₀) (θ₀ := θ₀) (e := e) (e' := e') (he := he) (deg := deg) (hX₀ := hX₀) (hA₀ := hA₀) (hE1 := hE1) (hE1mul := hE1mul) (hE1sc := hE1sc) (hE1' := hE1') (hE2 := hE2) (hE3 := hE3) (hE4 := hE4) (R₂ := R₂) (hR₂ := hR₂) (hR₂o := hR₂o) (hR₂r := hR₂r) (ê := ê) (hê := hê) (hE5a := hE5a) (hE5b1 := hE5b1) (hE5b2 := hE5b2) (hE5b3 := hE5b3) (hE5c := hE5c) (hE5d := hE5d) (hE5e := hE5e) (ι := ι) (Φ := Φ) (hΦ := hΦ) (hΦ4 := hΦ4) (MD := MD) (hMD := hMD) (η := η) (hη := hη) (E₀ := E₀) (hE₀ := hE₀) (eD := eD) (hnatD := hnatD) (hbijD := hbijD) (hfstD := hfstD) (hGLD := hGLD) (hPiD := hPiD) (hPiexD := hPiexD) (κ := κ) (hκ := hκ) (n₀ := n₀) (β₀ := β₀) (hβ₀ := hβ₀) (P₀ := P₀) (A₀w := A₀w) (aw := aw) (haw := haw) (aw' := aw') (haw' := haw') (kw := kw) (bw := bw) (hbw := hbw) (bw' := bw') (habw := habw) (hALw := hALw) (hBSw := hBSw) (hBSwlev := hBSwlev) (hJOINTw := hJOINTw) (Ξ := Ξ) (hΞleg := hΞleg) (hΞnat := hΞnat) (hΞiso := hΞiso) (hΞdef := hΞdef) (g₀ := g₀) (heqΓ := heqΓ) (heqW := heqW)
  have hnU : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsUnit ((n : ℕ) : B) := by
    intro B _ _
    have h := (CerednikDrinfeld.isUnit_natCast_of_not_dvd_of_card_quotient 𝒪 π hcomplete hres hunr n hrn).map (algebraMap 𝒪 B)
    rwa [map_natCast] at h
  have hrn' : Nat.Coprime r n := (Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).mpr hrn
  have hEX : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ r → IsUnit ((ℓ : ℕ) : B) → ∀ (K₀ : A₀.ExtraLevel ℓ), ∃ C : E.ExtraLevel ℓ,
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ.Eb.f),
                (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ.φ) ≫ ρ.gA) := by
    intro B _ _ _ ψ hB E ρ ℓ _ hℓr hℓu K₀
    exact TCLTransport.exists_C π A₀ ψ E hΛℤ hB ρ ℓ hℓr hℓu K₀

  have hEXN : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ₁ : Onr →ₐ[𝒪] B)
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
      (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ E)
      (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2), E.IsFormalModuleVia coord X θ →
      ∃ Pn : E.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn := by
    intro B _ _ _ ψ₁ hB hconn E ϱ X θ hθ
    obtain ⟨ψ₂, hψ₂⟩ : ∃ ψ₂ : Onr →ₐ[𝒪] B, frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ₂ = ψ₁ :=
      ⟨frobTwist Onr Fr (Multiplicative.toAdd (vdet g₀)) ψ₁, by rw [frobTwist_frobTwist, add_neg_cancel, frobTwist_zero]⟩
    subst hψ₂
    exact hC0e B hB hconn ψ₂ E ϱ X θ hθ
  have hUNN : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ₁ : Onr →ₐ[𝒪] B)
      (hB : IsNilpotent (algebraMap 𝒪 B π))
      (E : FakeEllipticCurve Λ N B) (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ₁ E) (Pn Pn' : E.FullLevel n),
      FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn →
      FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn' → Pn.P = Pn'.P := by
    intro B _ _ _ ψ₁ hB E ϱ Pn Pn' h h'
    obtain ⟨ψ₂, hψ₂⟩ : ∃ ψ₂ : Onr →ₐ[𝒪] B, frobTwist Onr Fr (- Multiplicative.toAdd (vdet g₀)) ψ₂ = ψ₁ :=
      ⟨frobTwist Onr Fr (Multiplicative.toAdd (vdet g₀)) ψ₁, by rw [frobTwist_frobTwist, add_neg_cancel, frobTwist_zero]⟩
    subst hψ₂
    exact hC0u B hB ψ₂ E ϱ Pn Pn' h h'
  intro B _ _ _ χ₀ hB hconn E ϱ₀ kk χ' hχ'
  subst hχ'
  have hcast : ∀ (χ₁ χ₂ : Onr →ₐ[𝒪] B) (h : χ₁ = χ₂) (ρ₁ : FakeEllipticCurve.Rigidification r π A₀ χ₁ E),
      ∃ ρ₂ : FakeEllipticCurve.Rigidification r π A₀ χ₂ E,
        Ξ B χ₂ hB ⟨E, ρ₂⟩ = Ξ B χ₁ hB ⟨E, ρ₁⟩ ∧
        (∀ (ℓ : ℕ) [Fact ℓ.Prime] (K₀ : A₀.ExtraLevel ℓ) (C : E.ExtraLevel ℓ),
          ((∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ₁.Eb.f),
                (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ₁.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ₁.φ) ≫ ρ₁.gA) ↔
           (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) (R : SchemeHomOver t' ρ₂.Eb.f),
                (∃ R₀ : T ⟶ C.K, R₀ ≫ C.levK = R.1 ≫ ρ₂.gb) → ∃ Q₀ : T ⟶ K₀.K, Q₀ ≫ K₀.levK = (R.1 ≫ ρ₂.φ) ≫ ρ₂.gA))) ∧
        (∀ Pn : E.FullLevel n,
          FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ₁ Pn ↔
          FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ₂ Pn) := by
    intro χ₁ χ₂ h ρ₁
    subst h
    exact ⟨ρ₁, rfl, fun _ _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  have hcomp : ∀ (x y z : ModuliPackage.GPoint 𝒪 MD B) (a b : ℤ),
      ModuliPackage.G.IsActBy ι Φ η Fr E₀ (Z ^ a) x y → ModuliPackage.G.IsActBy ι Φ η Fr E₀ (Z ^ b) y z →
      ModuliPackage.G.IsActBy ι Φ η Fr E₀ (Z ^ (a + b)) x z := by
    intro x y z a b h1 h2
    have h3 := Lmul B _ _ _ _ _ ((hGLD B hB _ _ _).mp h1) ((hGLD B hB _ _ _).mp h2)
    rw [← zpow_add, add_comm] at h3
    exact (hGLD B hB _ _ _).mpr h3
  have hid : ∀ x : ModuliPackage.GPoint 𝒪 MD B, ModuliPackage.G.IsActBy ι Φ η Fr E₀ (Z ^ (0 : ℤ)) x x := by
    intro x
    rw [zpow_zero]
    exact (hGLD B hB _ _ _).mpr (Lone B _)

  have hcoords : ∀ {χ₁ : Onr →ₐ[𝒪] B} (ρ₁ : FakeEllipticCurve.Rigidification r π A₀ χ₁ E) (Pn : E.FullLevel n),
      FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ₁ Pn →
      ∃ (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2), E.IsFormalModuleVia coord X θ := by
    intro χ₁ ρ₁ Pn h
    obtain ⟨-, -, -, X, θ, hXθ, -⟩ := h
    exact ⟨X, θ, hXθ⟩
  induction kk using Int.induction_on with
  | zero =>
      obtain ⟨ρ₀, hΞ₀, hTR₀, hN₀⟩ := hcast χ₀ (frobTwist Onr Fr 0 χ₀) (frobTwist_zero Fr χ₀).symm ϱ₀
      obtain ⟨⟨ρp, cp, -, hLp, -⟩, -⟩ := hXR B χ₀ hB hconn E ϱ₀
      refine ⟨ρ₀, 0, ?_, ?_, ?_⟩
      · rw [hΞ₀]; exact hid _
      · intro ℓ _ hℓ hℓu K₀ C C' hC hC' T t R
        obtain ⟨Cp, hCp⟩ := hEX B _ hB E ρp ℓ hℓ hℓu K₀
        have h1 := hLp ℓ hℓ hℓu K₀ C Cp hC hCp t R
        have h2 := hLp ℓ hℓ hℓu K₀ C' Cp ((hTR₀ ℓ K₀ C').mpr hC') hCp t R
        exact h1.trans h2.symm
      · intro Pn Pn' hPn hPn'
        have hPP := hUNN B χ₀ hB E ϱ₀ Pn Pn' hPn ((hN₀ Pn').mpr hPn')
        rw [hPP]
        simp
  | succ i ih =>
      obtain ⟨ρi, Ci, hAi, hLi, hNi⟩ := ih
      obtain ⟨⟨ρ'', c'', hA'', hL'', hN''⟩, -⟩ := hXR B _ hB hconn E ρi
      obtain ⟨ρs, hΞs, hTRs, hNs⟩ := hcast _ (frobTwist Onr Fr ((i : ℤ) + 1) χ₀) (by rw [frobTwist_frobTwist]) ρ''
      refine ⟨ρs, Ci + c'', ?_, ?_, ?_⟩
      · rw [hΞs]; exact hcomp _ _ _ _ _ hAi hA''
      · intro ℓ _ hℓ hℓu K₀ C C' hC hC' T t R
        obtain ⟨Ci', hCi'⟩ := hEX B _ hB E ρi ℓ hℓ hℓu K₀
        have h1 := hLi ℓ hℓ hℓu K₀ C Ci' hC hCi' t R
        have h2 := hL'' ℓ hℓ hℓu K₀ Ci' C' hCi' ((hTRs ℓ K₀ C').mpr hC') t R
        exact h1.trans h2
      · intro Pn Pn'' hPn hPn''
        obtain ⟨X, θ, hXθ⟩ := hcoords ϱ₀ Pn hPn
        obtain ⟨Pni, hPni⟩ := hEXN B _ hB hconn E ρi X θ hXθ
        have h1 := hNi Pn Pni hPn hPni
        have h2 := hN'' n (hnU B) P₀ Pni Pn'' hPni ((hNs Pn'').mpr hPn'')
        exact F530N.nsmulPt_chain E.L (𝟙 _) r n hrn' Pn.P Pni.P Pn''.P Pn.torsion Pn''.torsion Ci c'' h1 h2
  | pred i ih =>
      obtain ⟨ρi, Ci, hAi, hLi, hNi⟩ := ih
      obtain ⟨-, ⟨ρ'', c'', hA'', hL'', hN''⟩⟩ := hXR B _ hB hconn E ρi
      obtain ⟨ρs, hΞs, hTRs, hNs⟩ := hcast _ (frobTwist Onr Fr (-(i : ℤ) - 1) χ₀)
        (by rw [frobTwist_frobTwist, ← sub_eq_add_neg]) ρ''
      refine ⟨ρs, Ci + c'', ?_, ?_, ?_⟩
      · rw [hΞs]; exact hcomp _ _ _ _ _ hAi hA''
      · intro ℓ _ hℓ hℓu K₀ C C' hC hC' T t R
        obtain ⟨Ci', hCi'⟩ := hEX B _ hB E ρi ℓ hℓ hℓu K₀
        have h1 := hLi ℓ hℓ hℓu K₀ C Ci' hC hCi' t R
        have h2 := hL'' ℓ hℓ hℓu K₀ Ci' C' hCi' ((hTRs ℓ K₀ C').mpr hC') t R
        exact h1.trans h2
      · intro Pn Pn'' hPn hPn''
        obtain ⟨X, θ, hXθ⟩ := hcoords ϱ₀ Pn hPn
        obtain ⟨Pni, hPni⟩ := hEXN B _ hB hconn E ρi X θ hXθ
        have h1 := hNi Pn Pni hPn hPni
        have h2 := hN'' n (hnU B) P₀ Pni Pn'' hPni ((hNs Pn'').mpr hPn'')
        exact F530N.nsmulPt_chain E.L (𝟙 _) r n hrn' Pn.P Pni.P Pn''.P Pn.torsion Pn''.torsion Ci c'' h1 h2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_frobTwist_zpow_isActBy_scalar_extraLevel_normLevel_of_rigidifiedToG
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_rigidification_frobTwist_zpow_isActBy_scalar_extraLevel_normLevel_of_rigidifiedToG (solution)
