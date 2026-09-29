-- Prove2me | solution 1 for GaloisRepAdic.exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dc31f94c-e607-5c54-9099-282c42b3ce45

import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic

set_option autoImplicit false

namespace InertNeSol

variable {A : Type} [CommRing A] [IsLocalRing A]

private theorem of_odd (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ ≠ 1 := by
  have h2p : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hu2 : IsUnit (2 : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).mpr hcop
  obtain ⟨σ, hσP, hσμ⟩ := P.exists_mem_inertiaSubgroupIn_apply_eq_pow hp hP hu2.unit
  refine ⟨σ, hσP, fun hone => ?_⟩
  have hact : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ 1 = 1 → σ μ = μ ^ 2 := by
    intro μ hμ
    have hv : ((hu2.unit : (ZMod p)ˣ) : ZMod p).val = 2 := by
      rw [IsUnit.unit_spec]; exact ZMod.val_cast_of_lt h2p
    rw [pow_one] at hμ; rw [hσμ μ hμ, hv]
  have hcong : LinearMap.det (ρ.ρ σ) - (2 : A) ∈ Ideal.span {((p ^ 1 : ℕ) : A)} :=
    hdet.2 1 σ 2 hact
  rw [pow_one] at hcong; rw [hone, map_one] at hcong
  have h1 : (1 : A) ∈ Ideal.span {(p : A)} := by
    have : -(1 : A) ∈ Ideal.span {(p : A)} := by
      have heq : (1 : A) - (2 : A) = -(1 : A) := by ring
      rw [← heq]; exact_mod_cast hcong
    simpa using (Ideal.span {(p : A)}).neg_mem this
  have hpUnit : IsUnit (p : A) := by
    rw [Ideal.mem_span_singleton] at h1; exact isUnit_of_dvd_one h1
  exact IsLocalRing.notMem_maximalIdeal.mpr hpUnit hdet.1

private theorem of_two (ρ : GaloisRepAdic A) (hp0 : (2 : A) ≠ 0) (hdet : ρ.DetIsCyclotomic 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime 2) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ ≠ 1 := by
  obtain ⟨σ, hσP, hσζ⟩ :=
    P.exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one hP
  refine ⟨σ, hσP, fun hone => ?_⟩
  have hcong : LinearMap.det (ρ.ρ σ) - (3 : A) ∈ Ideal.span {((2 ^ 2 : ℕ) : A)} :=
    hdet.2 2 σ 3 (fun μ hμ => hσζ μ hμ)
  rw [hone, map_one] at hcong
  have h2 : (2 : A) ∈ Ideal.span {(4 : A)} := by
    have heq : -((1 : A) - (3 : A)) = (2 : A) := by ring
    have h4 : ((2 ^ 2 : ℕ) : A) = (4 : A) := by norm_num
    rw [h4] at hcong; rw [← heq]
    exact (Ideal.span {(4 : A)}).neg_mem (by exact_mod_cast hcong)
  rw [Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  have hmul : (2 : A) * (1 - 2 * c) = 0 := by
    have : (4 : A) * c = 2 * (2 * c) := by ring
    rw [this] at hc; linear_combination hc
  have h2c : (2 : A) * c ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).mul_mem_right c hdet.1
  have hunit : IsUnit (1 - 2 * c) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2c
  exact hp0 ((hunit.mul_left_eq_zero).mp hmul)

end InertNeSol

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime)
    (hp0 : (p : A) ≠ 0) (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ ≠ 1 := by
  have _ := hp0
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2; exact InertNeSol.of_two ρ (by exact_mod_cast hp0) hdet P hP
  · exact InertNeSol.of_odd ρ hp hp2 hdet P hP

end S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic
end P2MW
export P2MW.S_GaloisRepAdic_exists_mem_inertiaSubgroupIn_apply_ne_one_of_detIsCyclotomic (solution)
