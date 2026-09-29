-- Prove2me | solution 1 for ExtCitation.exists_kummerCharacter_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2e20a4ce-462d-5d04-8426-f86d74313ea9

import Mathlib
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Theorems.Thm_ExtCitation_LocalLevel_exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_kummerCharacter_ne_one
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open ExtCitation

theorem solution (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p) :
    ∃ t : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)), kummerCharacter p q hqp t ≠ 1 := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  obtain ⟨t, ht, hne⟩ := ExtCitation.LocalLevel.exists_mem_inertiaSubgroupIn_apply_ne_of_pow_eq_prime (q : ℕ)
    (Fact.out : p.Prime).two_le (not_dvd_of_ne p q hqp) (kummerRoot_pow p q)
  refine ⟨⟨t, ht⟩, fun h1 => hne ?_⟩
  rw [kummerCharacter_apply, ofAdd_eq_one] at h1
  change primeLocalToGlobal q t (kummerRoot p q) = kummerRoot p q
  rw [apply_kummerRoot p q, h1, ZMod.val_zero, pow_zero, one_mul]

end S_ExtCitation_exists_kummerCharacter_ne_one
end P2MW
export P2MW.S_ExtCitation_exists_kummerCharacter_ne_one (solution)
