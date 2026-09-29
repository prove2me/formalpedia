-- Prove2me | solution 1 for FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1a7c05e1-1743-5ad1-9ec9-c8f6402cdf3d

import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open scoped Pointwise

noncomputable section

namespace P2mChebotarevConj

p2m_open "NumberField Ideal NumberField.Ideal ValuationSubring"

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

theorem exists_liesOverPrime (L : Type*) [Field L] [CharZero L] {q : ℕ} (hq : q.Prime) :
    ∃ A : ValuationSubring L, A.LiesOverPrime q := by
  set R : Subring L := ⊥ with hR
  have hqR : ¬ IsUnit ((q : ℕ) : R) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have hsurj : ∀ r : R, ∃ n : ℤ, (n : R) = r := by
      rintro ⟨r, hr⟩
      obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hr
      exact ⟨n, Subtype.ext (by simp)⟩
    obtain ⟨a, ha⟩ := hsurj u
    obtain ⟨b, hb⟩ := hsurj ↑u⁻¹
    have hab : (a : R) * b = 1 := by rw [ha, hb, Units.mul_inv]
    have hab' : (a : L) * b = 1 := by
      have := congrArg (Subtype.val) hab
      simpa using this
    have haq : (a : L) = q := by
      have := congrArg (Subtype.val) (ha.trans hu)
      simpa using this
    have hint : (a * b : ℤ) = 1 := by exact_mod_cast hab'
    have ha1 : a = 1 ∨ a = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hint
    have hq2 := hq.two_le
    rcases ha1 with rfl | rfl
    · have : (q : L) = 1 := by simpa using haq.symm
      have : q = 1 := by exact_mod_cast this
      omega
    · have h1 : ((q : ℤ) : L) = ((-1 : ℤ) : L) := by push_cast; simpa using haq.symm
      have : (q : ℤ) = -1 := Int.cast_injective h1
      omega
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (Ideal.span {((q : ℕ) : R)})
    (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  exact ⟨B, hB ⟨_, Ideal.subset_span rfl, by simp⟩⟩

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

theorem placeIdeal_ne_bot [NumberField F] (hq : q.Prime) (hA : A.LiesOverPrime q) :
    placeIdeal A F ≠ ⊥ := by
  intro hbot
  have hq0 : (q : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  exact hq0 (by simpa [hbot] using natCast_mem_placeIdeal A F hA)

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

end OverPrime

section Restriction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F : Type*) [Field F] [NumberField F] [Algebra F L] [IsScalarTower ℚ F L] [Normal ℚ F]
variable (A : ValuationSubring L)

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

theorem inertia_eq_bot_of_notMem {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hram : ℓ ∉ (finite_ramifiedPrimes F).toFinset) {Q : Ideal (𝓞 F)} [Q.IsPrime]
    (hℓQ : (ℓ : 𝓞 F) ∈ Q) : Q.inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  by_contra hne
  exact hram ((finite_ramifiedPrimes F).mem_toFinset.mpr
    ⟨hℓ, Q, inferInstance, ne_bot_of_natCast_mem F hℓ hℓQ, hne, hℓQ⟩)

end Ramified

section FiniteLevel

variable (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]

theorem exists_prime_isArithFrobAt_rat (σ : F ≃ₐ[ℚ] F) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 F), P.IsMaximal ∧ (p : 𝓞 F) ∈ P ∧
      IsArithFrobAt ℤ σ P :=
  NumberField.exists_prime_isArithFrobAt_of_isGalois ℚ F σ S

end FiniteLevel

section Bridge

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl
scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.instIsAlgClosure ℚ
  rfl
  rfl
scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _

variable (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
  [Algebra F (AlgebraicClosure ℚ)]

theorem exists_of_ker_le
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ g * τ * g⁻¹ * σ⁻¹ ∈ H := by

  obtain ⟨ℓ, hℓ, hℓmem, P, hPmax, hℓP, hσP⟩ :=
    exists_prime_isArithFrobAt_rat F (AlgEquiv.restrictNormalHom F σ)
      (S ∪ (finite_ramifiedPrimes F).toFinset)
  rw [Finset.mem_union, not_or] at hℓmem
  obtain ⟨hℓS, hℓram⟩ := hℓmem

  obtain ⟨A, hA⟩ := exists_liesOverPrime (AlgebraicClosure ℚ) hℓ
  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hℓ A hA

  set Q : Ideal (𝓞 F) := placeIdeal A F with hQdef
  have hℓQ : (ℓ : 𝓞 F) ∈ Q := natCast_mem_placeIdeal A F hA
  have hτQ : IsArithFrobAt ℤ (AlgEquiv.restrictNormalHom F τ) Q :=
    isArithFrobAt_restrictNormalHom_of_isFrobeniusAt F A hℓ hA hτ
  haveI hPprime : P.IsPrime := hPmax.isPrime
  haveI hfinQ : Finite ((𝓞 F) ⧸ Q) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (placeIdeal_ne_bot A F hℓ hA)
  haveI hfinP : Finite ((𝓞 F) ⧸ P) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (ne_bot_of_natCast_mem F hℓ hℓP)

  have hτeq : AlgEquiv.restrictNormalHom F τ = arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q := by
    have hmem := hτQ.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q)
    rw [inertia_eq_bot_of_notMem F hℓ hℓram hℓQ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hσeq : AlgEquiv.restrictNormalHom F σ = arithFrobAt ℤ (F ≃ₐ[ℚ] F) P := by
    have hmem := hσP.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)
    rw [inertia_eq_bot_of_notMem F hℓ hℓram hℓP, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem

  have hunder : Q.under ℤ = P.under ℤ := by
    rw [under_eq_of_natCast_mem F hℓ (Ideal.IsPrime.ne_top inferInstance) hℓQ,
      under_eq_of_natCast_mem F hℓ hPmax.ne_top hℓP]
  have hconj : IsConj (AlgEquiv.restrictNormalHom F τ) (AlgEquiv.restrictNormalHom F σ) := by
    rw [hτeq, hσeq]
    exact isConj_arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q P hunder

  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) c
  refine ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, hker ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hg, hc, mul_inv_cancel]

end Bridge

end P2mChebotarevConj
p2m_reactivate "P2MW.S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker.P2mChebotarevConj"

end
p2m_reactivate "P2MW.S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker.P2mChebotarevConj"

theorem solution (F : Type) [Field F] [NumberField F]
    [IsGalois ℚ F] [Algebra F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ g * τ * g⁻¹ * σ⁻¹ ∈ H :=
  P2mChebotarevConj.exists_of_ker_le F hker S σ

end S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
end P2MW
export P2MW.S_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker (solution)
