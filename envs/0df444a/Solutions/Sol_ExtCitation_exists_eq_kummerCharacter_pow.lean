-- Prove2me | solution 1 for ExtCitation.exists_eq_kummerCharacter_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fcbfa327-ff34-56d4-bb85-174c7001c07b

import Mathlib
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_tame_generator_at_level
import Theorems.Thm_ExtCitation_exists_kummerCharacter_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_eq_kummerCharacter_pow
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open ExtCitation

namespace KummerPowAux

theorem eq_one_of_pow_prime_pow_eq_one {G : Type*} [Group G] [Fintype G] {p q : ℕ}
    [hp : Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) (hcard : Fintype.card G = p)
    {x : G} {a : ℕ} (hx : x ^ (q ^ a) = 1) : x = 1 := by
  have h1 : orderOf x ∣ q ^ a := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ p := hcard ▸ orderOf_dvd_card
  rcases (Nat.dvd_prime hp.out).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h1
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp.out hq).1 (hp.out.dvd_of_dvd_pow h1)).symm

theorem exists_pow_eq_of_ne_one {G : Type*} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime]
    (hcard : Fintype.card G = p) {c : G} (hc : c ≠ 1) (x : G) : ∃ m : ℕ, c ^ m = x := by
  have htop : Subgroup.zpowers c = ⊤ :=
    zpowers_eq_top_of_prime_card (by rw [Nat.card_eq_fintype_card, hcard]) hc
  have hx : x ∈ Subgroup.zpowers c := by rw [htop]; exact Subgroup.mem_top x
  rw [← mem_powers_iff_mem_zpowers] at hx
  exact hx

end KummerPowAux

open KummerPowAux in
theorem solution (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (χ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →* Multiplicative (ZMod p))
    (hχ : ∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
          primeLocalToGlobal q (i : primeLocalGaloisGroup q) ∈ F.fixingSubgroup → χ i = 1) :
    ∃ a : ℕ, χ = (kummerCharacter p q hqp) ^ a := by
  classical

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  have hq : (q : ℕ).Prime := q.2
  have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by
    rw [Fintype.card_multiplicative, ZMod.card]

  obtain ⟨φ, hφ⟩ := exists_isFrobeniusAt_apply_primeLocalToGlobal q

  have hαint : IsIntegral ℚ (kummerRoot p q) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (kummerRoot p q)).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {kummerRoot p q}) :=
    IntermediateField.adjoin.finiteDimensional hαint
  haveI : FiniteDimensional ℚ (F ⊔ IntermediateField.adjoin ℚ {kummerRoot p q} :
      IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_sup _ _
  obtain ⟨F', hF'fd, hF'gal, hFF', hαF'⟩ : ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      ∃ _ : FiniteDimensional ℚ F', ∃ _ : IsGalois ℚ F', F ≤ F' ∧ kummerRoot p q ∈ F' := by
    refine ⟨IntermediateField.normalClosure ℚ
        (F ⊔ IntermediateField.adjoin ℚ {kummerRoot p q} : IntermediateField ℚ (AlgebraicClosure ℚ))
        (AlgebraicClosure ℚ), inferInstance,
      { to_isSeparable := inferInstance, to_normal := normalClosure.normal ℚ _ (AlgebraicClosure ℚ) }, ?_, ?_⟩
    · exact le_sup_left.trans (IntermediateField.le_normalClosure _)
    · exact (le_sup_right.trans (IntermediateField.le_normalClosure _))
        (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
  haveI := hF'fd
  haveI := hF'gal

  have hχ' : ∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      primeLocalToGlobal q (i : primeLocalGaloisGroup q) ∈ F'.fixingSubgroup → χ i = 1 :=
    fun i hi => hχ i (IntermediateField.fixingSubgroup_antitone hFF' hi)
  have hκ' : ∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      primeLocalToGlobal q (i : primeLocalGaloisGroup q) ∈ F'.fixingSubgroup →
        kummerCharacter p q hqp i = 1 := by
    intro i hi
    rw [kummerCharacter_apply]
    have hfix : primeLocalToGlobal q (i : primeLocalGaloisGroup q) (kummerRoot p q) = kummerRoot p q :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi _ hαF'
    have h0 : kummerExp p q (primeLocalToGlobal q (i : primeLocalGaloisGroup q)) = ((0 : ℕ) : ZMod p) :=
      kummerExp_eq_of_apply_eq p q _ (n := 0) (by rw [pow_zero, one_mul]; exact hfix)
    rw [h0, Nat.cast_zero, ofAdd_zero]

  obtain ⟨t, W, htI, -, -, -, hWpow, hgen, -⟩ := exists_tame_generator_at_level q φ hφ F'

  have key : ∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      ∃ a : ℕ, ∀ ψ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →*
          Multiplicative (ZMod p),
        (∀ j : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
          primeLocalToGlobal q (j : primeLocalGaloisGroup q) ∈ F'.fixingSubgroup → ψ j = 1) →
        ψ i = ψ ⟨t, htI⟩ ^ a := by
    intro i
    obtain ⟨a, ha⟩ := hgen i i.2
    refine ⟨a, fun ψ hψ => ?_⟩

    have hwI : (t ^ a)⁻¹ * (i : primeLocalGaloisGroup q) ∈
        ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ htI a)) i.2
    obtain ⟨b, hb⟩ := hWpow _ ha
    have hψw : ψ ⟨(t ^ a)⁻¹ * i, hwI⟩ = 1 := by
      apply eq_one_of_pow_prime_pow_eq_one (a := b) hq hqp hcard
      rw [← map_pow]
      apply hψ
      rw [Subgroup.mem_comap] at hb
      simpa using hb
    have hdecomp : i = ⟨t, htI⟩ ^ a * ⟨(t ^ a)⁻¹ * i, hwI⟩ := by
      apply Subtype.ext
      simp [mul_inv_cancel_left]
    conv_lhs => rw [hdecomp]
    rw [map_mul, hψw, mul_one, map_pow]

  have hκt : kummerCharacter p q hqp ⟨t, htI⟩ ≠ 1 := by
    intro h1
    obtain ⟨t₀, ht₀⟩ := exists_kummerCharacter_ne_one p q hqp
    obtain ⟨a, ha⟩ := key t₀
    have := ha (kummerCharacter p q hqp) hκ'
    rw [h1, one_pow] at this
    exact ht₀ this

  obtain ⟨m, hm⟩ := exists_pow_eq_of_ne_one hcard hκt (χ ⟨t, htI⟩)
  refine ⟨m, MonoidHom.ext fun i => ?_⟩
  obtain ⟨a, ha⟩ := key i
  have hκm : ∀ j : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      primeLocalToGlobal q (j : primeLocalGaloisGroup q) ∈ F'.fixingSubgroup →
        (kummerCharacter p q hqp ^ m) j = 1 := by
    intro j hj
    rw [MonoidHom.pow_apply, hκ' j hj, one_pow]
  rw [ha χ hχ', ha _ hκm, MonoidHom.pow_apply, ← hm]

end S_ExtCitation_exists_eq_kummerCharacter_pow
end P2MW
export P2MW.S_ExtCitation_exists_eq_kummerCharacter_pow (solution)
