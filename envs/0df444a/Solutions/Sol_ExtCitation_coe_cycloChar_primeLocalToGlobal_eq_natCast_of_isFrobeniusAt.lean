-- Prove2me | solution 1 for ExtCitation.coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/30394719-edd2-5ad4-b4ac-4573604a871e

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_InertiaKummerCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    (p : ℕ) [Fact p.Prime] (q : Nat.Primes) (hqp : (q : ℕ) ≠ p)
    {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q) :
    ((cycloChar p (primeLocalToGlobal q φ) : (ZMod p)ˣ) : ZMod p) = ((q : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  symm
  refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (primeLocalToGlobal q φ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (fun t ht => ?_)
  have ht' : ((t : AlgebraicClosure ℚ)) ^ p = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  rw [ZMod.val_natCast]
  change primeLocalToGlobal q φ (t : AlgebraicClosure ℚ) = _
  rw [frobenius_smul_eq_pow_of_pow_eq_one q hφ (not_dvd_of_ne p q hqp) ht']
  conv_lhs => rw [← Nat.mod_add_div (q : ℕ) p, pow_add, pow_mul, ht', one_pow, mul_one]

end S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt
end P2MW
export P2MW.S_ExtCitation_coe_cycloChar_primeLocalToGlobal_eq_natCast_of_isFrobeniusAt (solution)
