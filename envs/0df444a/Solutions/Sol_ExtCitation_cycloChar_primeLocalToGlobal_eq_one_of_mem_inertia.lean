-- Prove2me | solution 1 for ExtCitation.cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fffcff5c-cd87-572e-9495-ee0fe520494b

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {σ : primeLocalGaloisGroup q}
    (hσ : σ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) :
    cycloChar p (primeLocalToGlobal q σ) = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : (1 : ZMod p) = (cycloChar p (primeLocalToGlobal q σ) : ZMod p) := by
    refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (primeLocalToGlobal q σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
    rw [ZMod.val_one, pow_one]
    have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    exact inertiaPullback_smul_eq_of_pow_eq_one q hσ (not_dvd_of_ne p q hqp) ht'
  exact Units.ext h1.symm

end S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
end P2MW
export P2MW.S_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia (solution)
