-- Prove2me | solution 1 for ExtCitation.exists_inertia_pCharacter_generator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c28856c7-b3b2-5c1b-b98d-76559f8d4ada

import Mathlib
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Theorems.Thm_ExtCitation_exists_eq_kummerCharacter_pow
import Theorems.Thm_ExtCitation_exists_kummerCharacter_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_inertia_pCharacter_generator
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open ExtCitation

namespace P2mS17K4p

theorem inertiaPullback_normal' (q : Nat.Primes) :
    (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).Normal := by
  have : ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)
      = (((primeLocalPlace q).inertiaSubgroup ℚ)).comap (toDecomp q) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map]
    constructor
    · rintro ⟨τ, hτ, hτg⟩
      have : toDecomp q g = τ := Subtype.ext hτg.symm
      rwa [this]
    · intro h; exact ⟨toDecomp q g, h, rfl⟩
  rw [this, ValuationSubring.inertiaSubgroup, MonoidHom.comap_ker]
  exact MonoidHom.normal_ker _

end P2mS17K4p

theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ∃ (t : primeLocalGaloisGroup q)
      (ht : t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))
      (hφt : φ * t * φ⁻¹ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
      ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
        (χ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →* Multiplicative (ZMod p)),
        (∀ i : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)),
          primeLocalToGlobal q (i : primeLocalGaloisGroup q) ∈ F.fixingSubgroup → χ i = 1) →
          (χ ⟨t, ht⟩ = 1 → χ = 1) ∧ χ ⟨φ * t * φ⁻¹, hφt⟩ = χ ⟨t, ht⟩ ^ (q : ℕ) := by
  haveI := P2mS17K4p.inertiaPullback_normal' q
  obtain ⟨t, htne⟩ := ExtCitation.exists_kummerCharacter_ne_one p q hqp
  have hφt : φ * (t : primeLocalGaloisGroup q) * φ⁻¹ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) :=
    Subgroup.Normal.conj_mem inferInstance _ t.2 φ
  refine ⟨t, t.2, hφt, fun F _ _ χ hχ => ?_⟩
  obtain ⟨a, rfl⟩ := ExtCitation.exists_eq_kummerCharacter_pow p q hqp F χ hχ
  have ht' : (⟨(t : primeLocalGaloisGroup q), t.2⟩ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))) = t :=
    Subtype.ext rfl
  constructor
  · intro h1
    rw [MonoidHom.pow_apply, ht'] at h1

    have hp : (p : ℕ).Prime := Fact.out
    have horder : orderOf (kummerCharacter p q hqp t) = p := by
      have h := orderOf_dvd_of_pow_eq_one (show kummerCharacter p q hqp t ^ p = 1 by
        rw [← ofAdd_toAdd (kummerCharacter p q hqp t), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero])
      rcases (Nat.dvd_prime hp).mp h with h0 | h0
      · exact absurd (orderOf_eq_one_iff.mp h0) htne
      · exact h0
    have hdvd : p ∣ a := by rw [← horder]; exact orderOf_dvd_of_pow_eq_one h1
    obtain ⟨b, rfl⟩ := hdvd
    ext σ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, pow_mul, ← ofAdd_toAdd (kummerCharacter p q hqp σ), ← ofAdd_nsmul,
      nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero, one_pow]
  · rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ht', ← pow_mul, mul_comm, pow_mul]
    congr 1
    have := kummerCharacter_conj p q hqp hφ t hφt
    exact this

end S_ExtCitation_exists_inertia_pCharacter_generator
end P2MW
export P2MW.S_ExtCitation_exists_inertia_pCharacter_generator (solution)
