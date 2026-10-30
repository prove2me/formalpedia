-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_sixth_power_actual_rows
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:27:27.343716+00:00
-- url     : https://prove2.me/submissions/8656e524-f9cc-44a7-ae81-040543ba5d89

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainContinuation
open Polynomial

theorem normalized_sixth_power_expansion (β : ℂ) :
    ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ) =
      C (1) * X^18 +
      C (-51) * X^16 +
      C (-816*β) * X^15 +
      C (4335/4) * X^14 +
      C (34680*β) * X^13 +
      C (277440*β^2 - 24565/2) * X^12 +
      C (-589560*β) * X^11 +
      C (1252815/16 - 9432960*β^2) * X^10 +
      C (-50309120*β^3 + 5011260*β) * X^9 +
      C (120270240*β^2 - 4259571/16) * X^8 +
      C (1282882560*β^3 - 21297855*β) * X^7 +
      C (5131530240*β^4 - 681531360*β^2 + 24137569/64) * X^6 +
      C (-10904501760*β^3 + 72412707*β/2) * X^5 +
      C (-87236014080*β^4 + 1448254140*β^2) * X^4 +
      C (-279155245056*β^5 + 30896088320*β^3) * X^3 +
      C (370753059840*β^4) * X^2 +
      C (2372819582976*β^5) * X^1 +
      C (6327518887936*β^6) * X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (β z : ℂ) :
    let p : Polynomial ℂ := (X^3-C (17/2)*X-136*C β)^6
    (derivative^[6] p).eval z = 13366080 * (25154560*β^4/91 - 2959360*β^3*z^3/13 + 6288640*β^3*z/13 + 179520*β^2*z^6/13 - 1387200*β^2*z^4/13 + 2358240*β^2*z^2/13 - 3340840*β^2/91 - 220*β*z^9 + 22440*β*z^7/7 - 190740*β*z^5/13 + 294780*β*z^3/13 - 417605*β*z/52 + z^12 - 22*z^10 + 2805*z^8/16 - 15895*z^6/26 + 368475*z^4/416 - 83521*z^2/208 + 1419857/69888) ∧
    (derivative^[7] p).eval z = 160392960 * (-739840*β^3*z^2/13 + 1572160*β^3/39 + 89760*β^2*z^5/13 - 462400*β^2*z^3/13 + 393040*β^2*z/13 - 165*β*z^8 + 1870*β*z^6 - 79475*β*z^4/13 + 73695*β*z^2/13 - 417605*β/624 + z^11 - 55*z^9/3 + 935*z^7/8 - 15895*z^5/52 + 122825*z^3/416 - 83521*z/1248) ∧
    (derivative^[8] p).eval z = 1764322560 * (-1479680*β^3*z/143 + 40800*β^2*z^4/13 - 1387200*β^2*z^2/143 + 393040*β^2/143 - 120*β*z^7 + 1020*β*z^5 - 28900*β*z^3/13 + 147390*β*z/143 + z^10 - 15*z^8 + 595*z^6/8 - 7225*z^4/52 + 368475*z^2/4576 - 83521/13728) ∧
    (derivative^[9] p).eval z = 17643225600 * (-147968*β^3/143 + 16320*β^2*z^3/13 - 277440*β^2*z/143 - 84*β*z^6 + 510*β*z^4 - 8670*β*z^2/13 + 14739*β/143 + z^9 - 12*z^7 + 357*z^5/8 - 1445*z^3/26 + 73695*z/4576) ∧
    (derivative^[10] p).eval z = 158789030400 * (5440*β^2*z^2/13 - 92480*β^2/429 - 56*β*z^5 + 680*β*z^3/3 - 5780*β*z/39 + z^8 - 28*z^6/3 + 595*z^4/24 - 1445*z^2/78 + 24565/13728) ∧
    (derivative^[11] p).eval z = 1270312243200 * (1360*β^2*z/13 - 35*β*z^4 + 85*β*z^2 - 1445*β/78 + z^7 - 7*z^5 + 595*z^3/48 - 1445*z/312) ∧
    (derivative^[12] p).eval z = 8892185702400 * (1360*β^2/91 - 20*β*z^3 + 170*β*z/7 + z^6 - 5*z^4 + 85*z^2/16 - 1445/2184) ∧
    (derivative^[13] p).eval z = 53353114214400 * (-10*β*z^2 + 85*β/21 + z^5 - 10*z^3/3 + 85*z/48) ∧
    (derivative^[14] p).eval z = 266765571072000 * (-4*β*z + z^4 - 2*z^2 + 17/48) ∧
    (derivative^[15] p).eval z = 1067062284288000 * (-β + z^3 - z) ∧
    (derivative^[16] p).eval z = 3201186852864000 * (z^2 - 1/3) ∧
    (derivative^[17] p).eval z = 6402373705728000 * (z) := by
  let p : Polynomial ℂ := (X^3-C (17/2)*X-136*C β)^6
  have hexpand := normalized_sixth_power_expansion β
  change p = _ at hexpand
  dsimp only
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  all_goals change (derivative^[_] p).eval z = _
  all_goals rw [hexpand]
  all_goals simp only [iterate_map_add,iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul,eval_add,eval_mul,eval_C,eval_pow,eval_X]
  all_goals norm_num [Nat.descFactorial] <;> ring
