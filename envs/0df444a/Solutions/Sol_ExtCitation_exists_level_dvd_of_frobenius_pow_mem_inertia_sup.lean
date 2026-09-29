-- Prove2me | solution 1 for ExtCitation.exists_level_dvd_of_frobenius_pow_mem_inertia_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5bad3acf-95c8-5796-bc77-190aa7c49c7f

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup

set_option autoImplicit false

open ExtCitation

namespace P2mS17K3

theorem mem_nonunits_comap {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

open scoped NNReal in
theorem padicPlace_liesOverPrime (q : ℕ) [Fact q.Prime] : (padicPlace q).LiesOverPrime q := by
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / (q : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ q := (Fact.out : q.Prime).two_le
  rw [ValuationSubring.LiesOverPrime, padicPlace, mem_nonunits_comap, ValuationSubring.mem_nonunits_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((padicEmbedding q) (q : AlgebraicClosure ℚ)) < 1
  rw [map_natCast, hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

theorem primeLocalPlace_liesOverPrime (q : Nat.Primes) : (primeLocalPlace q).LiesOverPrime q := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact padicPlace_liesOverPrime q

theorem primeLocalToGlobal_mem_decompositionSubgroup (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    primeLocalToGlobal q g ∈ (primeLocalPlace q).decompositionSubgroup ℚ := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g

theorem mem_inertiaPullback_iff (q : Nat.Primes) (g : primeLocalGaloisGroup q) :
    g ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ↔
      ∀ x : IsLocalRing.ResidueField (primeLocalPlace q),
        (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ :
          (primeLocalPlace q).decompositionSubgroup ℚ) • x = x := by
  rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτg⟩
    intro x
    have hmem : (⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩ : (primeLocalPlace q).decompositionSubgroup ℚ) = τ := by
      apply Subtype.ext; exact hτg.symm
    rw [hmem]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun φ => (φ : IsLocalRing.ResidueField (primeLocalPlace q) ≃+* _) x) hτ
    simpa using this
  · intro h
    refine ⟨⟨primeLocalToGlobal q g, primeLocalToGlobal_mem_decompositionSubgroup q g⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    simpa using h x

theorem eq_one_of_residue_eq_one_of_pow_eq_one {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {u : A} {m : ℕ} (hum : u ^ m = 1) (hm : (m : IsLocalRing.ResidueField A) ≠ 0)
    (hres : IsLocalRing.residue A u = 1) : u = 1 := by
  by_contra hu
  have h1 : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hum, sub_self]
  have h2 : ∑ i ∈ Finset.range m, u ^ i = 0 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hu)
  apply hm
  have := congrArg (IsLocalRing.residue A) h2
  rw [map_sum, map_zero] at this
  simpa [map_pow, hres] using this

theorem dvd_of_pow_sub_one_dvd_pow_sub_one {a n j : ℕ} (ha : 2 ≤ a) (h : a ^ n - 1 ∣ a ^ j - 1) : n ∣ j := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one a n j
  rw [Nat.gcd_eq_left h] at hg
  have h1 : 1 ≤ a ^ n := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ a ^ Nat.gcd n j := Nat.one_le_pow _ _ (by omega)
  have heq : a ^ Nat.gcd n j = a ^ n := by omega
  have := Nat.pow_right_injective ha heq
  rw [← this]
  exact Nat.gcd_dvd_right n j

end P2mS17K3

open P2mS17K3 in
theorem solution (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀] (n : ℕ) (hn : 0 < n) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F₀ ≤ F ∧ FiniteDimensional ℚ F ∧
      ∀ j : ℕ, φ ^ j ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
                        ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) → n ∣ j := by
  classical
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq2 : 2 ≤ (q : ℕ) := hqF.out.two_le

  let A : ValuationSubring (AlgebraicClosure ℚ) := primeLocalPlace q
  let κ := IsLocalRing.ResidueField A
  let D := A.decompositionSubgroup ℚ
  have hD : ∀ g : primeLocalGaloisGroup q, primeLocalToGlobal q g ∈ D := P2mS17K3.primeLocalToGlobal_mem_decompositionSubgroup q
  let rD : primeLocalGaloisGroup q →* D := (primeLocalToGlobal q).codRestrict D hD

  have hqκ : ((q : ℕ) : κ) = 0 := by
    have hlop : (primeLocalPlace q).LiesOverPrime q := P2mS17K3.primeLocalPlace_liesOverPrime q
    have h1 : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      simp at hlop ⊢
      exact hlop
    rw [← map_natCast (IsLocalRing.residue A), (IsLocalRing.residue_eq_zero_iff _).mpr h1]

  have hqn : (q : ℕ) ≤ (q : ℕ) ^ n := Nat.le_self_pow hn.ne' _
  have hm1 : 1 ≤ (q : ℕ) ^ n := by omega
  set m : ℕ := (q : ℕ) ^ n - 1 with hmdef
  have hm0 : m ≠ 0 := by omega
  have hmκ : (m : κ) ≠ 0 := by
    rw [hmdef, Nat.cast_sub hm1, Nat.cast_pow, hqκ, zero_pow hn.ne', Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  haveI : NeZero (m : ℚ) := ⟨by exact_mod_cast hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m
  have hζA : ζ ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff]
    have : (A.valuation ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' hm0).mp this).le
  let ζA : A := ⟨ζ, hζA⟩
  have hζAm : ζA ^ m = 1 := Subtype.ext (by simp [ζA, hζ.pow_eq_one])
  let ζκ : κ := IsLocalRing.residue A ζA
  have hζκ0 : ζκ ≠ 0 := by
    have : ζκ ^ m = 1 := by rw [← map_pow, hζAm, map_one]
    intro h0
    rw [h0, zero_pow hm0] at this
    exact zero_ne_one this

  have hζint : IsIntegral ℚ ζ := (hζ.isIntegral (Nat.pos_of_ne_zero hm0)).tower_top
  let Fz : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
  haveI : FiniteDimensional ℚ Fz := IntermediateField.adjoin.finiteDimensional hζint
  have hζFz : ζ ∈ Fz := IntermediateField.mem_adjoin_simple_self ℚ ζ
  refine ⟨F₀ ⊔ Fz, le_sup_left, IntermediateField.finiteDimensional_sup F₀ Fz, fun j hj => ?_⟩

  let H : Subgroup (primeLocalGaloisGroup q) := (MulAction.stabilizer D ζκ).comap rD
  have hI : ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ≤ H := by
    intro g hg
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    exact (P2mS17K3.mem_inertiaPullback_iff q g).mp hg ζκ
  have hU : ((F₀ ⊔ Fz).fixingSubgroup).comap (primeLocalToGlobal q) ≤ H := by
    intro g hg
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    have hfix : (primeLocalToGlobal q g) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_comap.mp hg) ζ
        ((le_sup_right : Fz ≤ F₀ ⊔ Fz) hζFz)
    change rD g • IsLocalRing.residue A ζA = IsLocalRing.residue A ζA
    rw [← IsLocalRing.ResidueField.residue_smul]
    congr 1
    apply Subtype.ext
    exact hfix
  have hφj : φ ^ j ∈ H := (sup_le hI hU) hj

  have hfrob : ∀ (k : ℕ) (x : κ), rD (φ ^ k) • x = x ^ ((q : ℕ) ^ k) := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, map_one, one_smul, pow_zero, pow_one]
    | succ k ih =>
      intro x
      rw [pow_succ, map_mul, mul_smul, (show rD φ • x = x ^ (q : ℕ) from hφ.smul_residue_eq x), smul_pow', ih,
        ← pow_mul, ← pow_succ]
  have hfixζ : ζκ ^ ((q : ℕ) ^ j) = ζκ := by
    have := hφj
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, hfrob] at this
    exact this

  have h1j : 1 ≤ (q : ℕ) ^ j := Nat.one_le_pow _ _ hqF.out.pos
  have hu_res : IsLocalRing.residue A (ζA ^ ((q : ℕ) ^ j - 1)) = 1 := by
    rw [map_pow]
    apply mul_right_cancel₀ hζκ0
    change ζκ ^ ((q : ℕ) ^ j - 1) * ζκ = 1 * ζκ
    rw [← pow_succ, Nat.sub_add_cancel h1j, one_mul]
    exact hfixζ
  have hu_pow : (ζA ^ ((q : ℕ) ^ j - 1)) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζAm, one_pow]
  have hu : ζA ^ ((q : ℕ) ^ j - 1) = 1 := eq_one_of_residue_eq_one_of_pow_eq_one hu_pow hmκ hu_res
  have hdvd : m ∣ (q : ℕ) ^ j - 1 := by
    rw [← hζ.pow_eq_one_iff_dvd]
    have := congrArg Subtype.val hu
    simpa [ζA] using this

  exact dvd_of_pow_sub_one_dvd_pow_sub_one hq2 hdvd

end S_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup
end P2MW
export P2MW.S_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup (solution)
