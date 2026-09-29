-- Prove2me | solution 1 for GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3893b5a5-0013-5266-8271-0d1f3548cd5e

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Pointwise

noncomputable section

namespace P2mChebotarevQ

p2m_open "NumberField Ideal NumberField.Ideal ValuationSubring Filter Topology"

section Place

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem smul_sub_pow_mem_nonunits
    {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ} (h : A.IsFrobeniusAt σ q)
    {x : L} (hx : x ∈ A) : σ x - x ^ q ∈ A.nonunits := by
  set a : A := ⟨x, hx⟩ with ha
  set g : A.decompositionSubgroup K := ⟨σ, h.mem_decompositionSubgroup⟩ with hg
  have h1 : IsLocalRing.residue A (g • a) = IsLocalRing.residue A (a ^ q) := by
    rw [map_pow, IsLocalRing.ResidueField.residue_smul]
    exact h.smul_residue_eq _
  have h2 : g • a - a ^ q ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (g • a - a ^ q) = 0 := by
      rw [map_sub, h1, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((g • a - a ^ q : A) : L) = σ x - x ^ q := rfl
  have := (coe_mem_nonunits_iff (A := A)).mpr h2
  rwa [hcoe] at this

theorem sub_mem_nonunits_of_mem_inertiaSubgroupIn
    {A : ValuationSubring L} {τ : L ≃ₐ[K] L} (h : τ ∈ A.inertiaSubgroupIn K)
    {x : L} (hx : x ∈ A) : τ x - x ∈ A.nonunits := by
  obtain ⟨d, hd, rfl⟩ := h
  set a : A := ⟨x, hx⟩ with ha
  have hker : ∀ y : IsLocalRing.ResidueField A, d • y = y := fun y => by
    have := RingEquiv.congr_fun (MonoidHom.mem_ker.1 hd) y
    simpa using this
  have h1 : IsLocalRing.residue A (d • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul]
    exact hker _
  have h2 : d • a - a ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (d • a - a) = 0 := by
      rw [map_sub, h1, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((d • a - a : A) : L) = (d : L ≃ₐ[K] L) x - x := rfl
  have := (coe_mem_nonunits_iff (A := A)).mpr h2
  rwa [hcoe] at this

end Place

section PlaceIdeal

variable {L : Type*} [Field L]
variable (A : ValuationSubring L) (F : Type*) [Field F] [Algebra F L]

theorem algebraMap_ringOfIntegers_mem (x : 𝓞 F) :
    algebraMap F L (algebraMap (𝓞 F) F x) ∈ A := by
  have hint : IsIntegral ℤ (algebraMap F L (algebraMap (𝓞 F) F x)) :=
    (RingOfIntegers.isIntegral_coe x).map ((algebraMap F L).toIntAlgHom)
  haveI : IsScalarTower ℤ A L := IsScalarTower.of_algebraMap_eq fun n => by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  have hintA : IsIntegral A (algebraMap F L (algebraMap (𝓞 F) F x)) := hint.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  exact ha ▸ a.2

def placeIdealHom : 𝓞 F →+* A :=
  ((algebraMap F L).comp (algebraMap (𝓞 F) F)).codRestrict A.toSubring
    (algebraMap_ringOfIntegers_mem A F)

@[scoped simp]
theorem coe_placeIdealHom_apply (x : 𝓞 F) :
    (placeIdealHom A F x : L) = algebraMap F L (algebraMap (𝓞 F) F x) :=
  rfl

def placeIdeal : Ideal (𝓞 F) :=
  (IsLocalRing.maximalIdeal A).comap (placeIdealHom A F)

theorem mem_placeIdeal_iff {x : 𝓞 F} :
    x ∈ placeIdeal A F ↔ algebraMap F L (algebraMap (𝓞 F) F x) ∈ A.nonunits := by
  unfold placeIdeal
  rw [Ideal.mem_comap, ← coe_mem_nonunits_iff, coe_placeIdealHom_apply]

scoped instance : (placeIdeal A F).IsPrime := by
  unfold placeIdeal
  haveI : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  exact Ideal.IsPrime.comap _

variable {q : ℕ}

theorem natCast_mem_placeIdeal (hA : A.LiesOverPrime q) : (q : 𝓞 F) ∈ placeIdeal A F := by
  rw [mem_placeIdeal_iff, map_natCast, map_natCast]
  exact hA

end PlaceIdeal

section OverPrime

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in

theorem under_eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)} (hQ : Q ≠ ⊤)
    (hqQ : (q : 𝓞 F) ∈ Q) : Q.under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hq)).irreducible
  have h1 : Ideal.span {(q : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap,
      map_natCast]
    exact hqQ
  have h2 : Q.under ℤ ≠ ⊤ := Ideal.comap_ne_top _ hQ
  exact (hmax.eq_of_le h2 h1).symm

omit [NumberField F] in

theorem card_quotient_under_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)}
    (hQ : Q ≠ ⊤) (hqQ : (q : 𝓞 F) ∈ Q) : Nat.card (ℤ ⧸ Q.under ℤ) = q := by
  rw [under_eq_of_natCast_mem F hq hQ hqQ,
    Nat.card_congr (Int.quotientSpanNatEquivZMod q).toEquiv, Nat.card_zmod]

theorem ne_bot_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)}
    (hqQ : (q : 𝓞 F) ∈ Q) : Q ≠ ⊥ := by
  intro hbot
  have hq0 : (q : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  exact hq0 (by simpa [hbot] using hqQ)

theorem isMaximal_of_isPrime_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)}
    (hQ : Q.IsPrime) (hqQ : (q : 𝓞 F) ∈ Q) : Q.IsMaximal :=
  hQ.isMaximal (ne_bot_of_natCast_mem F hq hqQ)

end OverPrime

section Restriction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F : Type*) [Field F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L] [Normal ℚ F]
variable (A : ValuationSubring L)

theorem algebraMap_restrictNormalHom_smul (τ : L ≃ₐ[ℚ] L) (x : 𝓞 F) :
    algebraMap F L (algebraMap (𝓞 F) F (AlgEquiv.restrictNormalHom F τ • x)) =
      τ (algebraMap F L (algebraMap (𝓞 F) F x)) := by
  have hsmul : algebraMap (𝓞 F) F (AlgEquiv.restrictNormalHom F τ • x) =
      AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x) := rfl
  have h : AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)
      = τ.restrictNormal F (algebraMap (𝓞 F) F x) := rfl
  rw [hsmul, h, AlgEquiv.restrictNormal_commutes]

theorem isArithFrobAt_restrictNormalHom_of_isFrobeniusAt {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) {τ : L ≃ₐ[ℚ] L} (hτ : A.IsFrobeniusAt τ ℓ) :
    IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) (placeIdeal A F) := by
  intro x
  have hne : placeIdeal A F ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  rw [card_quotient_under_of_natCast_mem F hℓ hne (natCast_mem_placeIdeal A F hA),
    mem_placeIdeal_iff]
  have hsmul : algebraMap (𝓞 F) F
      (MulSemiringAction.toAlgHom ℤ (𝓞 F) (AlgEquiv.restrictNormalHom F τ) x) =
      AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x) := rfl
  have hrestrict : algebraMap F L (AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)) =
      τ (algebraMap F L (algebraMap (𝓞 F) F x)) := by
    have h : AlgEquiv.restrictNormalHom F τ (algebraMap (𝓞 F) F x)
        = τ.restrictNormal F (algebraMap (𝓞 F) F x) := rfl
    rw [h, AlgEquiv.restrictNormal_commutes]
  rw [map_sub, map_pow, map_sub, map_pow, hsmul, hrestrict]
  exact smul_sub_pow_mem_nonunits hτ (algebraMap_ringOfIntegers_mem A F x)

theorem restrictNormalHom_mem_inertia_of_mem_inertiaSubgroupIn {τ : L ≃ₐ[ℚ] L}
    (hτ : τ ∈ A.inertiaSubgroupIn ℚ) :
    AlgEquiv.restrictNormalHom F τ ∈ (placeIdeal A F).inertia (F ≃ₐ[ℚ] F) := by
  intro x
  rw [Submodule.mem_toAddSubgroup, mem_placeIdeal_iff, map_sub, map_sub,
    algebraMap_restrictNormalHom_smul]
  exact sub_mem_nonunits_of_mem_inertiaSubgroupIn hτ (algebraMap_ringOfIntegers_mem A F x)

end Restriction

section Ramified

variable (F : Type*) [Field F] [NumberField F]

theorem exists_smul_ne_of_ne_one {ι : F ≃ₐ[ℚ] F} (hι : ι ≠ 1) :
    ∃ x : 𝓞 F, ι • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 F, ι • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hι (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (K := F) z
  have hx : ι (algebraMap (𝓞 F) F x) = algebraMap (𝓞 F) F x := congrArg (algebraMap (𝓞 F) F)
    (hcon x)
  have hy' : ι (algebraMap (𝓞 F) F y) = algebraMap (𝓞 F) F y := congrArg (algebraMap (𝓞 F) F)
    (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

theorem finite_setOf_isPrime_le {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    {Q : Ideal (𝓞 F) | Q.IsPrime ∧ I ≤ Q}.Finite := by
  haveI : Finite ((𝓞 F) ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Finite (Ideal ((𝓞 F) ⧸ I)) :=
    Finite.of_injective (fun J : Ideal ((𝓞 F) ⧸ I) => (J : Set ((𝓞 F) ⧸ I)))
      fun _ _ h => SetLike.coe_injective h
  refine Set.Finite.of_finite_image (f := fun Q => Q.map (Ideal.Quotient.mk I))
    (Set.toFinite _) ?_
  rintro Q₁ ⟨-, hIQ₁⟩ Q₂ ⟨-, hIQ₂⟩ heq
  have key : ∀ Q : Ideal (𝓞 F), I ≤ Q →
      (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    intro Q hIQ
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIQ]
  rw [← key Q₁ hIQ₁, ← key Q₂ hIQ₂]
  exact congrArg _ heq

theorem finite_setOf_isMaximal_natCast_mem {p : ℕ} (hp : p.Prime) :
    {P : Ideal (𝓞 F) | P.IsMaximal ∧ (p : 𝓞 F) ∈ P}.Finite := by
  refine (finite_setOf_isPrime_le F (I := Ideal.span {(p : 𝓞 F)}) ?_).subset ?_
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  · rintro P ⟨hP, hpP⟩
    exact ⟨hP.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hpP⟩

def displacementIdeal (ι : F ≃ₐ[ℚ] F) : Ideal (𝓞 F) :=
  Ideal.span (Set.range fun x : 𝓞 F => ι • x - x)

theorem displacementIdeal_ne_bot {ι : F ≃ₐ[ℚ] F} (hι : ι ≠ 1) :
    displacementIdeal F ι ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_smul_ne_of_ne_one F hι
  intro hbot
  exact hx (sub_eq_zero.mp (Ideal.span_eq_bot.mp hbot _ ⟨x, rfl⟩))

theorem displacementIdeal_le_iff {ι : F ≃ₐ[ℚ] F} {Q : Ideal (𝓞 F)} :
    displacementIdeal F ι ≤ Q ↔ ι ∈ Q.inertia (F ≃ₐ[ℚ] F) := by
  rw [displacementIdeal, Ideal.span_le]
  constructor
  · intro h x
    exact h ⟨x, rfl⟩
  · rintro h - ⟨x, rfl⟩
    exact h x

theorem finite_setOf_inertia_ne_bot :
    {Q : Ideal (𝓞 F) | Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥}.Finite := by
  have hsub : {Q : Ideal (𝓞 F) | Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥} ⊆
      ⋃ ι ∈ {ι : F ≃ₐ[ℚ] F | ι ≠ 1},
        {Q : Ideal (𝓞 F) | Q.IsPrime ∧ displacementIdeal F ι ≤ Q} := by
    rintro Q ⟨hQp, -, hQi⟩
    obtain ⟨ι, hιQ, hι1⟩ := (Q.inertia (F ≃ₐ[ℚ] F)).bot_or_exists_ne_one.resolve_left hQi
    refine Set.mem_biUnion (show (ι : F ≃ₐ[ℚ] F) ∈ {ι : F ≃ₐ[ℚ] F | ι ≠ 1} from ?_) ?_
    · simpa using hι1
    · exact ⟨hQp, displacementIdeal_le_iff F |>.mpr hιQ⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Set.toFinite _) ?_) hsub
  intro ι hι
  exact Set.Finite.subset (finite_setOf_isPrime_le F (displacementIdeal_ne_bot F hι))
    fun Q hQ => ⟨hQ.1, hQ.2⟩

omit [NumberField F] in
theorem subsingleton_setOf_prime_natCast_mem {Q : Ideal (𝓞 F)} (hQ : Q ≠ ⊤) :
    {ℓ : ℕ | ℓ.Prime ∧ (ℓ : 𝓞 F) ∈ Q}.Subsingleton := by
  rintro ℓ ⟨hℓ, hℓQ⟩ ℓ' ⟨hℓ', hℓ'Q⟩
  by_contra hne
  apply hQ
  rw [Ideal.eq_top_iff_one]
  have hcop : Nat.Coprime ℓ ℓ' := (Nat.coprime_primes hℓ hℓ').mpr hne
  have hbezout : (1 : ℤ) = ℓ * Nat.gcdA ℓ ℓ' + ℓ' * Nat.gcdB ℓ ℓ' := by
    have := Nat.gcd_eq_gcd_ab ℓ ℓ'
    rwa [hcop, Nat.cast_one] at this
  have : (1 : 𝓞 F) = (ℓ : 𝓞 F) * (algebraMap ℤ (𝓞 F) (Nat.gcdA ℓ ℓ')) +
      (ℓ' : 𝓞 F) * (algebraMap ℤ (𝓞 F) (Nat.gcdB ℓ ℓ')) := by
    have := congrArg (algebraMap ℤ (𝓞 F)) hbezout
    push_cast at this ⊢
    simpa using this
  rw [this]
  exact Q.add_mem (Q.mul_mem_right _ hℓQ) (Q.mul_mem_right _ hℓ'Q)

theorem finite_ramifiedPrimes :
    {ℓ : ℕ | ℓ.Prime ∧ ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥ ∧ (ℓ : 𝓞 F) ∈ Q}.Finite := by
  have hsub : {ℓ : ℕ | ℓ.Prime ∧ ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥ ∧ (ℓ : 𝓞 F) ∈ Q} ⊆
      ⋃ Q ∈ {Q : Ideal (𝓞 F) | Q.IsPrime ∧ Q ≠ ⊥ ∧ Q.inertia (F ≃ₐ[ℚ] F) ≠ ⊥},
        {ℓ : ℕ | ℓ.Prime ∧ (ℓ : 𝓞 F) ∈ Q} := by
    rintro ℓ ⟨hℓ, Q, hQp, hQb, hQi, hℓQ⟩
    exact Set.mem_biUnion ⟨hQp, hQb, hQi⟩ ⟨hℓ, hℓQ⟩
  refine Set.Finite.subset (Set.Finite.biUnion (finite_setOf_inertia_ne_bot F) ?_) hsub
  rintro Q ⟨hQp, -, -⟩
  exact (subsingleton_setOf_prime_natCast_mem F hQp.ne_top).finite

def ramifiedPrimes : Finset ℕ := (finite_ramifiedPrimes F).toFinset

theorem inertia_eq_bot_of_notMem {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hram : ℓ ∉ ramifiedPrimes F) {Q : Ideal (𝓞 F)} [Q.IsPrime]
    (hℓQ : (ℓ : 𝓞 F) ∈ Q) : Q.inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  by_contra hne
  exact hram ((finite_ramifiedPrimes F).mem_toFinset.mpr
    ⟨hℓ, Q, inferInstance, ne_bot_of_natCast_mem F hℓ hℓQ, hne, hℓQ⟩)

end Ramified

section Counting

variable (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]

def overSet (p : ℕ) : Set (Ideal (𝓞 F)) := {P | P.IsMaximal ∧ (p : 𝓞 F) ∈ P}

def frobSet (g : F ≃ₐ[ℚ] F) (p : ℕ) : Set (Ideal (𝓞 F)) :=
  {P | P.IsMaximal ∧ (p : 𝓞 F) ∈ P ∧ IsArithFrobAt ℤ g P}

def frobCount (g : F ≃ₐ[ℚ] F) (p : ℕ) : ℕ := (frobSet F g p).ncard

theorem frobSet_subset (g : F ≃ₐ[ℚ] F) (p : ℕ) : frobSet F g p ⊆ overSet F p :=
  fun _ h => ⟨h.1, h.2.1⟩

theorem overSet_finite {p : ℕ} (hp : p.Prime) : (overSet F p).Finite :=
  finite_setOf_isMaximal_natCast_mem F hp

theorem frobSet_finite (g : F ≃ₐ[ℚ] F) {p : ℕ} (hp : p.Prime) : (frobSet F g p).Finite :=
  (overSet_finite F hp).subset (frobSet_subset F g p)

theorem overSet_subset_orbit {p : ℕ} (hp : p.Prime) {P₀ : Ideal (𝓞 F)} (hP₀ : P₀ ∈ overSet F p) :
    overSet F p ⊆ MulAction.orbit (F ≃ₐ[ℚ] F) P₀ := by
  intro P hP
  haveI : P₀.IsPrime := hP₀.1.isPrime
  haveI : P.IsPrime := hP.1.isPrime
  have hunder : P₀.under ℤ = P.under ℤ := by
    rw [under_eq_of_natCast_mem F hp hP₀.1.ne_top hP₀.2,
      under_eq_of_natCast_mem F hp hP.1.ne_top hP.2]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 F) (F ≃ₐ[ℚ] F) P₀ P hunder
  exact ⟨g, hg.symm⟩

theorem orbit_subset_overSet {p : ℕ} (hp : p.Prime) {P₀ : Ideal (𝓞 F)}
    (hP₀ : P₀ ∈ overSet F p) : MulAction.orbit (F ≃ₐ[ℚ] F) P₀ ⊆ overSet F p := by
  rintro P ⟨g, rfl⟩
  haveI : P₀.IsPrime := hP₀.1.isPrime
  have hgp : g • (p : 𝓞 F) = p := map_natCast (MulSemiringAction.toRingHom _ (𝓞 F) g) p
  have hmem : (p : 𝓞 F) ∈ g • P₀ := by
    have := Ideal.smul_mem_pointwise_smul g _ P₀ hP₀.2
    rwa [hgp] at this
  have hprime : (g • P₀).IsPrime := inferInstance
  exact ⟨isMaximal_of_isPrime_of_natCast_mem F hp hprime hmem, hmem⟩

theorem ncard_overSet_le {p : ℕ} (hp : p.Prime) :
    (overSet F p).ncard ≤ Nat.card (F ≃ₐ[ℚ] F) := by
  by_cases hne : (overSet F p).Nonempty
  · obtain ⟨P₀, hP₀⟩ := hne
    have horb : (MulAction.orbit (F ≃ₐ[ℚ] F) P₀).Finite :=
      Set.finite_range _
    calc (overSet F p).ncard ≤ (MulAction.orbit (F ≃ₐ[ℚ] F) P₀).ncard :=
          Set.ncard_le_ncard (overSet_subset_orbit F hp hP₀) horb
      _ = (MulAction.stabilizer (F ≃ₐ[ℚ] F) P₀).index := (MulAction.index_stabilizer _ P₀).symm
      _ ≤ Nat.card (F ≃ₐ[ℚ] F) := Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty]
    exact Nat.zero_le _

theorem frobCount_le (g : F ≃ₐ[ℚ] F) {p : ℕ} (hp : p.Prime) :
    frobCount F g p ≤ Nat.card (F ≃ₐ[ℚ] F) :=
  (Set.ncard_le_ncard (frobSet_subset F g p) (overSet_finite F hp)).trans (ncard_overSet_le F hp)

theorem eq_of_isArithFrobAt_of_notMem {p : ℕ} (hp : p.Prime) (hram : p ∉ ramifiedPrimes F)
    {P : Ideal (𝓞 F)} (hP : P ∈ overSet F p) {g g' : F ≃ₐ[ℚ] F}
    (hg : IsArithFrobAt ℤ g P) (hg' : IsArithFrobAt ℤ g' P) : g = g' := by
  haveI : P.IsPrime := hP.1.isPrime
  have hmem := hg.mul_inv_mem_inertia hg'
  rw [inertia_eq_bot_of_notMem F hp hram hP.2, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

theorem orderOf_le_card_stabilizer {P : Ideal (𝓞 F)} (hP : P.IsMaximal) {g : F ≃ₐ[ℚ] F}
    (hg : IsArithFrobAt ℤ g P) :
    orderOf g ≤ Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) P) := by
  haveI : P.IsPrime := hP.isPrime
  have hmem : g ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) P := hg.mem_stabilizer
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.orderOf_dvd_natCard _ hmem)

theorem card_stabilizer_smul (g : F ≃ₐ[ℚ] F) (P : Ideal (𝓞 F)) :
    Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) (g • P)) =
      Nat.card (MulAction.stabilizer (F ≃ₐ[ℚ] F) P) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • P = g • P)).toEquiv).symm

theorem sum_orderOf_mul_frobCount_le {p : ℕ} (hp : p.Prime) (hram : p ∉ ramifiedPrimes F) :
    ∑ g : F ≃ₐ[ℚ] F, orderOf g * frobCount F g p ≤ Nat.card (F ≃ₐ[ℚ] F) := by
  classical
  set G := F ≃ₐ[ℚ] F
  set S : Finset (Ideal (𝓞 F)) := (overSet_finite F hp).toFinset with hS
  have hmemS : ∀ {P}, P ∈ S ↔ P ∈ overSet F p := fun {P} => (overSet_finite F hp).mem_toFinset

  have hcount : ∀ g : G, frobCount F g p =
      ∑ P ∈ S, (if IsArithFrobAt ℤ g P then 1 else 0) := by
    intro g
    have hset : frobSet F g p = ↑(S.filter fun P => IsArithFrobAt ℤ g P) := by
      ext P
      simp only [frobSet, Set.mem_setOf_eq, Finset.coe_filter, hmemS, overSet]
      tauto
    rw [frobCount, hset, Set.ncard_coe_finset, Finset.card_filter]

  have hswap : ∑ g : G, orderOf g * frobCount F g p =
      ∑ P ∈ S, ∑ g : G, (if IsArithFrobAt ℤ g P then orderOf g else 0) := by
    simp_rw [hcount, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    exact Finset.sum_comm
  rw [hswap]

  have hinner : ∀ P ∈ S, ∑ g : G, (if IsArithFrobAt ℤ g P then orderOf g else 0) ≤
      Nat.card (MulAction.stabilizer G P) := by
    intro P hPS
    have hP : P ∈ overSet F p := hmemS.mp hPS
    by_cases hex : ∃ g : G, IsArithFrobAt ℤ g P
    · obtain ⟨g₀, hg₀⟩ := hex
      have heq : ∀ g : G, (if IsArithFrobAt ℤ g P then orderOf g else 0) =
          if g = g₀ then orderOf g₀ else 0 := by
        intro g
        by_cases hg : IsArithFrobAt ℤ g P
        · have : g = g₀ := eq_of_isArithFrobAt_of_notMem F hp hram hP hg hg₀
          subst this
          simp [hg]
        · have : g ≠ g₀ := fun h => hg (h ▸ hg₀)
          simp [hg, this]
      rw [Finset.sum_congr rfl fun g _ => heq g, Finset.sum_ite_eq' Finset.univ g₀,
        if_pos (Finset.mem_univ _)]
      exact orderOf_le_card_stabilizer F hP.1 hg₀
    · push Not at hex
      rw [Finset.sum_congr rfl fun g _ => if_neg (hex g), Finset.sum_const_zero]
      exact Nat.zero_le _
  refine (Finset.sum_le_sum hinner).trans ?_

  by_cases hne : S.Nonempty
  · obtain ⟨P₀, hP₀S⟩ := hne
    have hP₀ : P₀ ∈ overSet F p := hmemS.mp hP₀S
    have hconst : ∀ P ∈ S, Nat.card (MulAction.stabilizer G P) =
        Nat.card (MulAction.stabilizer G P₀) := by
      intro P hPS
      obtain ⟨g, rfl⟩ := overSet_subset_orbit F hp hP₀ (hmemS.mp hPS)
      exact card_stabilizer_smul F g P₀
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    have hSorb : (S : Set (Ideal (𝓞 F))) = MulAction.orbit G P₀ := by
      apply Set.Subset.antisymm
      · intro P hP
        exact overSet_subset_orbit F hp hP₀ (hmemS.mp hP)
      · intro P hP
        exact hmemS.mpr (orbit_subset_overSet F hp hP₀ hP)
    have hcardS : S.card = (MulAction.stabilizer G P₀).index := by
      rw [MulAction.index_stabilizer, ← hSorb, Set.ncard_coe_finset]
    rw [hcardS, mul_comm, Subgroup.card_mul_index]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty]
    exact Nat.zero_le _

end Counting

section Preimage

theorem ncard_preimage_mul_card {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) (C : Set Q) :
    (f ⁻¹' C).ncard * Nat.card Q = C.ncard * Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite Q

  have hG : Nat.card G = Nat.card Q * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

  have hfib : ∀ c : Q, (f ⁻¹' {c}).ncard = Nat.card f.ker := fun c => by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf c)
  have hpre : (f ⁻¹' C).ncard = C.ncard * Nat.card f.ker := by
    have hmaps : Set.MapsTo f ↑(f ⁻¹' C).toFinset ↑C.toFinset := by
      intro x hx
      simp only [Set.coe_toFinset, Set.mem_preimage] at hx ⊢
      exact hx
    rw [Set.ncard_eq_toFinset_card' (f ⁻¹' C), Finset.card_eq_sum_card_fiberwise hmaps,
      Set.ncard_eq_toFinset_card' C]
    have hterm : ∀ c ∈ C.toFinset,
        ((f ⁻¹' C).toFinset.filter fun x => f x = c).card = Nat.card f.ker := by
      intro c hc
      rw [Set.mem_toFinset] at hc
      rw [← hfib c, Set.ncard_eq_toFinset_card' (f ⁻¹' {c})]
      congr 1
      ext x
      simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨h ▸ hc, h⟩
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  rw [hpre, hG]
  ring

end Preimage

section FiniteLevel

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ <;> first | rfl | exact Subsingleton.elim _ _
scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem exists_finite_normal_level {M : Type} [Group M] (π : Γ →* M)
    (hπc : GaloisFactorsThroughFiniteLevel π) :
    ∃ E : IntermediateField ℚ ℚbar, FiniteDimensional ℚ E ∧ Normal ℚ E ∧
      ∀ σ : Γ, (∀ x : ℚbar, x ∈ E → σ x = x) → π σ = 1 := by
  obtain ⟨L₀, hfd, hL₀⟩ := hπc
  haveI := hfd
  refine ⟨IntermediateField.normalClosure ℚ L₀ ℚbar, inferInstance,
    normalClosure.normal ℚ L₀ ℚbar,
    fun σ hσ => hL₀ σ fun x hx => hσ x (IntermediateField.le_normalClosure L₀ hx)⟩

variable (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
  [Algebra F ℚbar] [IsScalarTower ℚ F ℚbar]

theorem place_conditions_of_frobCount_ne_zero
    {Q : Type} [Group Q] (π : Γ →* Q) (πbar : (F ≃ₐ[ℚ] F) →* Q)
    (hcomp : ∀ σ : Γ, πbar (AlgEquiv.restrictNormalHom F σ) = π σ)
    (C : Set Q) (hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C)
    {p : ℕ} (hp : p.Prime) (hram : p ∉ ramifiedPrimes F)
    {g : F ≃ₐ[ℚ] F} (hgC : πbar g ∈ C) (hcnt : frobCount F g p ≠ 0) :
    (∀ A : ValuationSubring ℚbar, A.LiesOverPrime p →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
      ∃ A : ValuationSubring ℚbar, A.LiesOverPrime p ∧
        ∃ σ : Γ, A.IsFrobeniusAt σ p ∧ π σ ∈ C := by
  refine ⟨fun A hA σ hσ => ?_, ?_⟩
  ·
    have hmem := restrictNormalHom_mem_inertia_of_mem_inertiaSubgroupIn F A hσ
    rw [inertia_eq_bot_of_notMem F hp hram (natCast_mem_placeIdeal A F hA),
      Subgroup.mem_bot] at hmem
    rw [← hcomp, hmem, map_one]
  ·
    obtain ⟨A, τ, hA, hτ⟩ :=
      ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, hp⟩

    set Q₀ : Ideal (𝓞 F) := placeIdeal A F with hQ₀def
    have hpQ₀ : (p : 𝓞 F) ∈ Q₀ := natCast_mem_placeIdeal A F hA
    have hτQ₀ : IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) Q₀ :=
      isArithFrobAt_restrictNormalHom_of_isFrobeniusAt F A hp hA hτ
    have hQ₀ : Q₀ ∈ overSet F p :=
      ⟨isMaximal_of_isPrime_of_natCast_mem F hp inferInstance hpQ₀, hpQ₀⟩

    obtain ⟨P, hPmax, hpP, hgP⟩ := Set.nonempty_of_ncard_ne_zero hcnt
    have hP : P ∈ overSet F p := ⟨hPmax, hpP⟩
    obtain ⟨h, hh⟩ := overSet_subset_orbit F hp hP hQ₀
    have hconj : IsArithFrobAt ℤ (h * g * h⁻¹) Q₀ := by
      rw [← hh]
      exact hgP.conj h

    have heq : AlgEquiv.restrictNormalHom F τ = h * g * h⁻¹ :=
      eq_of_isArithFrobAt_of_notMem F hp hram hQ₀ hτQ₀ hconj
    refine ⟨A, hA, τ, hτ, ?_⟩
    rw [← hcomp, heq, map_mul, map_mul, map_inv]
    exact hC _ _ hgC

end FiniteLevel

section Analytic

theorem tsum_primes_eq_tsum_indicator (G : ℕ → ℝ) :
    ∑' p : Nat.Primes, G p = ∑' n : ℕ, {n : ℕ | n.Prime}.indicator G n :=
  tsum_subtype {n : ℕ | n.Prime} G

theorem rpow_neg_nonneg (s : ℝ) (n : ℕ) : 0 ≤ (n : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem rpow_neg_le_one {s : ℝ} (hs : 0 < s) (n : ℕ) : (n : ℝ) ^ (-s) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
    exact zero_le_one
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

theorem summable_rpow_neg {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
  Real.summable_nat_rpow.mpr (by linarith)

theorem summable_indicator_mul_rpow {s : ℝ} (hs : 1 < s) {a : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (haB : ∀ n : ℕ, n.Prime → a n ≤ B) :
    Summable fun n : ℕ => {n : ℕ | n.Prime}.indicator (fun n => a n * (n : ℝ) ^ (-s)) n := by
  have hB : 0 ≤ B := (ha0 2).trans (haB 2 Nat.prime_two)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) ((summable_rpow_neg hs).mul_left B)
  · exact Set.indicator_nonneg (fun m _ => mul_nonneg (ha0 m) (rpow_neg_nonneg s m)) _
  · by_cases hn : n ∈ {n : ℕ | n.Prime}
    · rw [Set.indicator_of_mem hn]
      exact mul_le_mul_of_nonneg_right (haB n hn) (rpow_neg_nonneg s n)
    · rw [Set.indicator_of_notMem hn]
      exact mul_nonneg hB (rpow_neg_nonneg s n)

theorem le_mul_log_of_lt {K δ s : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hs : 1 < s)
    (hs' : s < 1 + Real.exp (-(K / δ))) : K ≤ δ * Real.log (1 / (s - 1)) := by
  have hpos : 0 < s - 1 := by linarith
  have h1 : s - 1 < Real.exp (-(K / δ)) := by linarith
  have h2 : Real.log (s - 1) < -(K / δ) := by
    have := Real.log_lt_log hpos h1
    rwa [Real.log_exp] at this
  have h3 : K / δ < Real.log (1 / (s - 1)) := by
    rw [one_div, Real.log_inv]
    linarith
  have h4 : K < δ * Real.log (1 / (s - 1)) := by
    have := (div_lt_iff₀ hδ).mp h3
    linarith [this]
  exact h4.le

end Analytic

section Main

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem main {Q : Type} [Group Q] [Finite Q] (π : Γ →* Q) (hπ : Function.Surjective π)
    (hπc : GaloisFactorsThroughFiniteLevel π)
    (C : Set Q) (hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C : ℝ) / Nat.card Q - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : {p : ℕ // p.Prime ∧
            (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
              ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
            ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
              ∃ σ : Γ, A.IsFrobeniusAt σ p ∧ π σ ∈ C},
          ((p : ℕ) : ℝ) ^ (-s) := by
  classical

  obtain ⟨E, hEfd, hEnormal, hEπ⟩ := exists_finite_normal_level π hπc
  haveI := hEfd
  haveI := hEnormal
  letI : NumberField E :=
    { to_charZero := inferInstance, to_finiteDimensional := hEfd }
  haveI : IsGalois ℚ E := isGalois_iff.mpr ⟨inferInstance, hEnormal⟩
  set res : Γ →* (E ≃ₐ[ℚ] E) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚbar) E with hres
  have hres_surj : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective ℚbar
  have hker : res.ker ≤ π.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    refine hEπ σ fun x hx => ?_
    have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨x, hx⟩
    have h2 : σ.restrictNormal E = 1 := hσ
    rw [h2, AlgEquiv.one_apply] at h1
    exact h1.symm
  set πbar : (E ≃ₐ[ℚ] E) →* Q := res.liftOfSurjective hres_surj ⟨π, hker⟩ with hπbar
  have hcomp : ∀ σ : Γ, πbar (res σ) = π σ := fun σ =>
    res.liftOfRightInverse_comp_apply _ _ ⟨π, hker⟩ σ
  have hπbar_surj : Function.Surjective πbar := fun q => by
    obtain ⟨σ, rfl⟩ := hπ q
    exact ⟨res σ, hcomp σ⟩

  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card (E ≃ₐ[ℚ] E) = n := ⟨_, rfl⟩
  have hn0 : 0 < n := hn ▸ Nat.card_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨Ct, hCt⟩ : ∃ Ct : Finset (E ≃ₐ[ℚ] E), Ct = Finset.univ.filter fun g => πbar g ∈ C :=
    ⟨_, rfl⟩
  have hmemCt : ∀ {g : E ≃ₐ[ℚ] E}, g ∈ Ct ↔ πbar g ∈ C := fun {g} => by
    rw [hCt, Finset.mem_filter]
    simp
  have hCt_le : (Ct.card : ℝ) ≤ n := by
    have : Ct.card ≤ n := by
      rw [← hn, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    exact_mod_cast this
  have hratio : (Ct.card : ℝ) / n = (Nat.card C : ℝ) / Nat.card Q := by
    have hQ0 : (0 : ℝ) < Nat.card Q := by exact_mod_cast (Nat.card_pos (α := Q))
    have hpre : (πbar ⁻¹' C) = ↑Ct := by
      ext g
      rw [Set.mem_preimage, Finset.mem_coe, hmemCt]
    have hkey := ncard_preimage_mul_card πbar hπbar_surj C
    rw [hpre, Set.ncard_coe_finset, ← Nat.card_coe_set_eq, hn] at hkey
    have hkeyR : (Ct.card : ℝ) * Nat.card Q = (Nat.card C : ℝ) * n := by exact_mod_cast hkey
    rw [div_eq_div_iff hnR.ne' hQ0.ne']
    exact hkeyR
  have hratio_le : (Nat.card C : ℝ) / Nat.card Q ≤ 1 := by
    rw [← hratio, div_le_one hnR]
    exact hCt_le

  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = δ / (2 * n) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  have hδ'n : (n : ℝ) * δ' = δ / 2 := by rw [hδ']; field_simp
  choose s₀ hs₀ hchild using fun g : E ≃ₐ[ℚ] E =>
    NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt E g δ' hδ'0

  obtain ⟨Ram, hRam⟩ : ∃ Ram : Finset ℕ, Ram = ramifiedPrimes E := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (n : ℝ) * n * Ram.card := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hδ2 : 0 < δ / 2 := by positivity
  set s₁ : ℝ := Finset.univ.inf' ⟨1, Finset.mem_univ _⟩ s₀ with hs₁
  have hs₁1 : 1 < s₁ := (Finset.lt_inf'_iff _).mpr fun g _ => hs₀ g
  set s₂ : ℝ := 1 + Real.exp (-(K / (δ / 2))) with hs₂
  have hs₂1 : 1 < s₂ := by rw [hs₂]; linarith [Real.exp_pos (-(K / (δ / 2)))]
  refine ⟨min (min s₁ s₂) 2, lt_min (lt_min hs₁1 hs₂1) one_lt_two, fun s hs hslt => ?_⟩
  have hss₁ : s < s₁ := hslt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hss₂ : s < s₂ := hslt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hs2 : s < 2 := hslt.trans_le (min_le_right _ _)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (1 / (s - 1)) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < s - 1)]
    linarith
  rw [← hL]

  set Tc : ℕ → Prop := fun p =>
    (∀ A : ValuationSubring ℚbar, A.LiesOverPrime p → ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
      ∃ A : ValuationSubring ℚbar, A.LiesOverPrime p ∧
        ∃ σ : Γ, A.IsFrobeniusAt σ p ∧ π σ ∈ C with hTc

  set c : (E ≃ₐ[ℚ] E) → ℕ → ℝ := fun g p => (frobCount E g p : ℝ) with hc
  set a : ℕ → ℝ := fun p => (∑ g ∈ Ct, (orderOf g : ℝ) * c g p) / n with ha
  have hc0 : ∀ g p, 0 ≤ c g p := fun g p => by simp only [hc]; positivity
  have hcle : ∀ g {p : ℕ}, p.Prime → c g p ≤ n := fun g p hp => by
    have := frobCount_le E g hp
    rw [hn] at this
    simp only [hc]
    exact_mod_cast this
  have hord : ∀ g : E ≃ₐ[ℚ] E, (orderOf g : ℝ) ≤ n := fun g => by
    have := orderOf_le_card (x := g)
    rw [hn] at this
    exact_mod_cast this
  have hord0 : ∀ g : E ≃ₐ[ℚ] E, (0 : ℝ) < orderOf g := fun g => by
    exact_mod_cast orderOf_pos g
  have ha0 : ∀ p, 0 ≤ a p := fun p => by
    simp only [ha]
    exact div_nonneg (Finset.sum_nonneg fun g _ => mul_nonneg (hord0 g).le (hc0 g p)) hnR.le

  have ha_crude : ∀ {p : ℕ}, p.Prime → a p ≤ (n : ℝ) * n := fun {p} hp => by
    simp only [ha]
    rw [div_le_iff₀ hnR]
    calc ∑ g ∈ Ct, (orderOf g : ℝ) * c g p ≤ ∑ g ∈ Ct, (n : ℝ) * n :=
          Finset.sum_le_sum fun g _ => mul_le_mul (hord g) (hcle g hp) (hc0 g p) hnR.le
      _ = Ct.card * ((n : ℝ) * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * ((n : ℝ) * n) := by gcongr
      _ = (n : ℝ) * n * n := by ring

  have ha_one : ∀ {p : ℕ}, p.Prime → p ∉ Ram → a p ≤ 1 := fun {p} hp hpr => by
    simp only [ha]
    rw [div_le_one hnR]
    have h1 : ∑ g ∈ Ct, (orderOf g : ℝ) * c g p ≤
        ∑ g : E ≃ₐ[ℚ] E, (orderOf g : ℝ) * c g p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun g _ _ => mul_nonneg (hord0 g).le (hc0 g p)
    have h2 : ∑ g : E ≃ₐ[ℚ] E, (orderOf g : ℝ) * c g p ≤ n := by
      have := sum_orderOf_mul_frobCount_le E hp (hRam ▸ hpr)
      rw [hn] at this
      simp only [hc]
      exact_mod_cast this
    exact h1.trans h2

  have ha_T : ∀ {p : ℕ}, p.Prime → p ∉ Ram → a p ≠ 0 → Tc p := fun {p} hp hpr hap => by
    have : ∃ g ∈ Ct, (orderOf g : ℝ) * c g p ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hap (by simp only [ha]; rw [Finset.sum_eq_zero hall, zero_div])
    obtain ⟨g, hgCt, hg⟩ := this
    have hcnt : frobCount E g p ≠ 0 := by
      intro h0
      exact hg (by simp only [hc]; rw [h0, Nat.cast_zero, mul_zero])
    exact place_conditions_of_frobCount_ne_zero E π πbar hcomp C hC hp (hRam ▸ hpr)
      (hmemCt.mp hgCt) hcnt

  obtain ⟨iT, hiT1, hiT0⟩ : ∃ iT : ℕ → ℝ, (∀ m, Tc m → iT m = 1) ∧ ∀ m, ¬ Tc m → iT m = 0 :=
    ⟨fun m => if Tc m then 1 else 0, fun m hm => if_pos hm, fun m hm => if_neg hm⟩
  have hiT_nonneg : ∀ m, 0 ≤ iT m := fun m => by
    by_cases hm : Tc m
    · rw [hiT1 m hm]; exact zero_le_one
    · rw [hiT0 m hm]
  have hiT_le : ∀ m, iT m ≤ 1 := fun m => by
    by_cases hm : Tc m
    · rw [hiT1 m hm]
    · rw [hiT0 m hm]; exact zero_le_one
  obtain ⟨iR, hiR1, hiR0⟩ : ∃ iR : ℕ → ℝ, (∀ m, m ∈ Ram → iR m = 1) ∧ ∀ m, m ∉ Ram → iR m = 0 :=
    ⟨fun m => if m ∈ Ram then 1 else 0, fun m hm => if_pos hm, fun m hm => if_neg hm⟩
  have hiR_nonneg : ∀ m, 0 ≤ iR m := fun m => by
    by_cases hm : m ∈ Ram
    · rw [hiR1 m hm]; exact zero_le_one
    · rw [hiR0 m hm]
  have hiR_le : ∀ m, iR m ≤ 1 := fun m => by
    by_cases hm : m ∈ Ram
    · rw [hiR1 m hm]
    · rw [hiR0 m hm]; exact zero_le_one
  have hab : ∀ {p : ℕ}, p.Prime → a p ≤ iT p + (n : ℝ) * n * iR p := fun {p} hp => by
    by_cases hpr : p ∈ Ram
    · rw [hiR1 p hpr, mul_one]
      have := ha_crude hp
      have h0 := hiT_nonneg p
      linarith
    · rw [hiR0 p hpr, mul_zero, add_zero]
      by_cases hap : a p = 0
      · rw [hap]; exact hiT_nonneg p
      · rw [hiT1 p (ha_T hp hpr hap)]
        exact ha_one hp hpr

  set f : ℕ → ℝ := fun m => (m : ℝ) ^ (-s) with hf
  have hf0 : ∀ m, 0 ≤ f m := rpow_neg_nonneg s
  have hf1 : ∀ m, f m ≤ 1 := rpow_neg_le_one (by linarith)
  set Pr : Set ℕ := {m : ℕ | m.Prime} with hPr

  have hDg : ∀ g : E ≃ₐ[ℚ] E, (1 / (orderOf g : ℝ) - δ') * L ≤
      ∑' m : ℕ, Pr.indicator (fun m => c g m * f m) m := fun g => by
    have h := hchild g s hs (hss₁.trans_le (Finset.inf'_le _ (Finset.mem_univ g)))
    rw [← hL] at h
    exact h.trans_eq (tsum_primes_eq_tsum_indicator (fun m => c g m * f m))
  have hsumm_g : ∀ g : E ≃ₐ[ℚ] E, Summable fun m : ℕ => Pr.indicator (fun m => c g m * f m) m :=
    fun g => summable_indicator_mul_rpow hs (hc0 g) (B := n) fun m hm => hcle g hm

  have hlow : ((Nat.card C : ℝ) / Nat.card Q - δ / 2) * L ≤
      ∑ g ∈ Ct, ((orderOf g : ℝ) / n) * ∑' m : ℕ, Pr.indicator (fun m => c g m * f m) m := by
    have hterm : ∀ g ∈ Ct, (1 / (n : ℝ) - δ') * L ≤
        ((orderOf g : ℝ) / n) * ∑' m : ℕ, Pr.indicator (fun m => c g m * f m) m := by
      intro g _
      have h1 : (orderOf g : ℝ) / n * (1 / orderOf g) = 1 / n := by
        have hog : (orderOf g : ℝ) ≠ 0 := (hord0 g).ne'
        field_simp
      have h2 : (orderOf g : ℝ) / n * δ' ≤ δ' :=
        mul_le_of_le_one_left hδ'0.le ((div_le_one hnR).mpr (hord g))
      have h3 : 1 / (n : ℝ) - δ' ≤ (orderOf g : ℝ) / n * (1 / orderOf g - δ') := by
        rw [mul_sub, h1]
        linarith
      calc (1 / (n : ℝ) - δ') * L ≤ ((orderOf g : ℝ) / n * (1 / orderOf g - δ')) * L :=
            mul_le_mul_of_nonneg_right h3 hL0
        _ = (orderOf g : ℝ) / n * ((1 / orderOf g - δ') * L) := by ring
        _ ≤ (orderOf g : ℝ) / n * ∑' m : ℕ, Pr.indicator (fun m => c g m * f m) m :=
            mul_le_mul_of_nonneg_left (hDg g) (by positivity)
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    refine le_trans ?_ hsum
    have h4 : (Ct.card : ℝ) * (1 / n) = (Nat.card C : ℝ) / Nat.card Q := by
      rw [← hratio]; ring
    have h5 : (Ct.card : ℝ) * δ' ≤ δ / 2 := by
      rw [← hδ'n]
      exact mul_le_mul_of_nonneg_right hCt_le hδ'0.le
    have h6 : ((Nat.card C : ℝ) / Nat.card Q - δ / 2) ≤ Ct.card * (1 / (n : ℝ) - δ') := by
      rw [mul_sub, h4]
      linarith
    calc ((Nat.card C : ℝ) / Nat.card Q - δ / 2) * L ≤ (Ct.card * (1 / (n : ℝ) - δ')) * L :=
          mul_le_mul_of_nonneg_right h6 hL0
      _ = Ct.card * ((1 / (n : ℝ) - δ') * L) := by ring

  have hswap : ∑ g ∈ Ct, ((orderOf g : ℝ) / n) * ∑' m : ℕ, Pr.indicator (fun m => c g m * f m) m
      = ∑' m : ℕ, Pr.indicator (fun m => a m * f m) m := by
    have h1 : ∀ g ∈ Ct, ((orderOf g : ℝ) / n) * ∑' m : ℕ, Pr.indicator (fun m => c g m * f m) m
        = ∑' m : ℕ, ((orderOf g : ℝ) / n) * Pr.indicator (fun m => c g m * f m) m :=
      fun g _ => tsum_mul_left.symm
    rw [Finset.sum_congr rfl h1,
      ← Summable.tsum_finsetSum (fun g _ => (hsumm_g g).mul_left _)]
    refine tsum_congr fun m => ?_
    by_cases hm : m ∈ Pr
    · simp only [Set.indicator_of_mem hm, ha]
      rw [Finset.sum_div, Finset.sum_mul]
      exact Finset.sum_congr rfl fun g _ => by ring
    · simp only [Set.indicator_of_notMem hm, mul_zero, Finset.sum_const_zero]

  have hsumm_a : Summable fun m : ℕ => Pr.indicator (fun m => a m * f m) m :=
    summable_indicator_mul_rpow hs ha0 (B := (n : ℝ) * n) fun m hm => ha_crude hm
  have hsumm_T : Summable fun m : ℕ => Pr.indicator (fun m => iT m * f m) m :=
    summable_indicator_mul_rpow hs hiT_nonneg (B := 1) fun m _ => hiT_le m
  have hsumm_R : Summable fun m : ℕ => Pr.indicator (fun m => iR m * f m) m :=
    summable_indicator_mul_rpow hs hiR_nonneg (B := 1) fun m _ => hiR_le m
  have hcmp : ∑' m : ℕ, Pr.indicator (fun m => a m * f m) m ≤
      ∑' m : ℕ, Pr.indicator (fun m => iT m * f m) m +
        (n : ℝ) * n * ∑' m : ℕ, Pr.indicator (fun m => iR m * f m) m := by
    rw [← tsum_mul_left, ← (hsumm_T.tsum_add (hsumm_R.mul_left _))]
    refine Summable.tsum_le_tsum (fun m => ?_) hsumm_a (hsumm_T.add (hsumm_R.mul_left _))
    by_cases hm : m ∈ Pr
    · simp only [Set.indicator_of_mem hm]
      calc a m * f m ≤ (iT m + (n : ℝ) * n * iR m) * f m :=
            mul_le_mul_of_nonneg_right (hab hm) (hf0 m)
        _ = _ := by ring
    · simp only [Set.indicator_of_notMem hm, mul_zero, add_zero, le_refl]

  have hT : ∑' m : ℕ, Pr.indicator (fun m => iT m * f m) m =
      ∑' p : {p : ℕ // p.Prime ∧ Tc p}, f p := by
    have hind : Pr.indicator (fun m => iT m * f m) = {p : ℕ | p.Prime ∧ Tc p}.indicator f := by
      funext m
      by_cases hm : m ∈ Pr
      · rw [Set.indicator_of_mem hm]
        by_cases hT : Tc m
        · rw [hiT1 m hT, one_mul, Set.indicator_of_mem (show m ∈ {p : ℕ | p.Prime ∧ Tc p} from
            ⟨hm, hT⟩)]
        · rw [hiT0 m hT, zero_mul, Set.indicator_of_notMem (show m ∉ {p : ℕ | p.Prime ∧ Tc p} from
            fun h => hT h.2)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem
          (show m ∉ {p : ℕ | p.Prime ∧ Tc p} from fun h => hm h.1)]
    rw [hind]
    exact (tsum_subtype {p : ℕ | p.Prime ∧ Tc p} f).symm

  have hR : ∑' m : ℕ, Pr.indicator (fun m => iR m * f m) m ≤ Ram.card := by
    have hle : ∀ m, Pr.indicator (fun m => iR m * f m) m ≤
        (↑Ram : Set ℕ).indicator (fun _ => (1 : ℝ)) m := by
      intro m
      by_cases hm : m ∈ Pr
      · rw [Set.indicator_of_mem hm]
        by_cases hmR : m ∈ Ram
        · rw [hiR1 m hmR, one_mul, Set.indicator_of_mem (Finset.mem_coe.mpr hmR)]
          exact hf1 m
        · rw [hiR0 m hmR, zero_mul, Set.indicator_of_notMem (fun h => hmR (Finset.mem_coe.mp h))]
      · rw [Set.indicator_of_notMem hm]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hfin : ∀ m ∉ Ram, (↑Ram : Set ℕ).indicator (fun _ => (1 : ℝ)) m = 0 :=
      fun m hm => Set.indicator_of_notMem (fun h => hm (Finset.mem_coe.mp h)) _
    calc ∑' m : ℕ, Pr.indicator (fun m => iR m * f m) m
        ≤ ∑' m : ℕ, (↑Ram : Set ℕ).indicator (fun _ => (1 : ℝ)) m :=
          Summable.tsum_le_tsum hle hsumm_R (summable_of_ne_finset_zero hfin)
      _ = ∑ m ∈ Ram, (↑Ram : Set ℕ).indicator (fun _ => (1 : ℝ)) m := tsum_eq_sum hfin
      _ ≤ ∑ m ∈ Ram, (1 : ℝ) := Finset.sum_le_sum fun m _ =>
          Set.indicator_le_self' (fun _ _ => zero_le_one) m
      _ = Ram.card := by simp

  have hKL : K ≤ δ / 2 * L := hL ▸ le_mul_log_of_lt hK0 hδ2 hs (by rwa [hs₂] at hss₂)
  have hRK : (n : ℝ) * n * ∑' m : ℕ, Pr.indicator (fun m => iR m * f m) m ≤ K := by
    rw [hK]
    exact mul_le_mul_of_nonneg_left hR (by positivity)

  have h1 := hlow.trans_eq hswap
  have h3 := hRK.trans hKL
  have h4 := h1.trans (hcmp.trans (add_le_add le_rfl h3))
  rw [hT] at h4
  have e1 : ((Nat.card C : ℝ) / Nat.card Q - δ) * L =
      ((Nat.card C : ℝ) / Nat.card Q - δ / 2) * L - δ / 2 * L := by ring
  rw [e1]
  exact sub_le_iff_le_add.mpr h4

end Main

end P2mChebotarevQ
p2m_reactivate "P2MW.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective.P2mChebotarevQ"

end
p2m_reactivate "P2MW.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective.P2mChebotarevQ"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem solution
    {Q : Type} [Group Q] [Finite Q] (π : Γℚ →* Q) (hπ : Function.Surjective π)
    (hπc : GaloisFactorsThroughFiniteLevel π)
    (C : Set Q) (hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C : ℝ) / Nat.card Q - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : {p : ℕ // p.Prime ∧
            (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
              ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
            ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
              ∃ σ : Γℚ, A.IsFrobeniusAt σ p ∧ π σ ∈ C},
          ((p : ℕ) : ℝ) ^ (-s) :=
  P2mChebotarevQ.main π hπ hπc C hC δ hδ

end S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
end P2MW
export P2MW.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective (solution)
