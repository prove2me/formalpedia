-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_seventh_power_actual_rows
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:45:22.13099+00:00
-- url     : https://prove2.me/submissions/dfdeb37a-40b7-46f4-9af6-6bd1dcca34e7

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

theorem normalized_seventh_power_expansion (β : ℂ) :
    ((X^3-C (10)*X-190*C β)^7 : Polynomial ℂ) =
      C (1) * X^21 +
      C (-70) * X^19 +
      C (-1330*β) * X^18 +
      C (2100) * X^17 +
      C (79800*β) * X^16 +
      C (758100*β^2 - 35000) * X^15 +
      C (-1995000*β) * X^14 +
      C (350000 - 37905000*β^2) * X^13 +
      C (-240065000*β^3 + 26600000*β) * X^12 +
      C (758100000*β^2 - 2100000) * X^11 +
      C (9602600000*β^3 - 199500000*β) * X^10 +
      C (45612350000*β^4 - 7581000000*β^2 + 7000000) * X^9 +
      C (-144039000000*β^3 + 798000000*β) * X^8 +
      C (-1368370500000*β^4 + 37905000000*β^2 - 10000000) * X^7 +
      C (-5199807900000*β^5 + 960260000000*β^3 - 1330000000*β) * X^6 +
      C (13683705000000*β^4 - 75810000000*β^2) * X^5 +
      C (103996158000000*β^5 - 2400650000000*β^3) * X^4 +
      C (329321167000000*β^6 - 45612350000000*β^4) * X^3 +
      C (-519980790000000*β^5) * X^2 +
      C (-3293211670000000*β^6) * X^1 +
      C (-8938717390000000*β^7) * X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (β z : ℂ) :
    let p : Polynomial ℂ := (X^3-C (10)*X-190*C β)^7
    (derivative^[7] p).eval z = 586051200 * (240065000*β^4*z^2/17 - 600162500*β^4/51 - 27797000*β^3*z^5/17 + 505400000*β^3*z^3/51 - 505400000*β^3*z/51 + 1426425*β^2*z^8/34 - 9509500*β^2*z^6/17 + 36575000*β^2*z^4/17 - 39900000*β^2*z^2/17 + 16625000*β^2/51 - 364*β*z^11 + 400400*β*z^9/51 - 1001000*β*z^7/17 + 3080000*β*z^5/17 - 3500000*β*z^3/17 + 2800000*β*z/51 + z^14 - 91*z^12/3 + 20020*z^10/57 - 625625*z^8/323 + 5005000*z^6/969 - 1925000*z^4/323 + 700000*z^2/323 - 250000/2907) ∧
    (derivative^[8] p).eval z = 8204716800 * (34295000*β^4*z/17 - 9927500*β^3*z^4/17 + 36100000*β^3*z^2/17 - 36100000*β^3/51 + 407550*β^2*z^7/17 - 4075500*β^2*z^5/17 + 10450000*β^2*z^3/17 - 5700000*β^2*z/17 - 286*β*z^10 + 85800*β*z^8/17 - 500500*β*z^6/17 + 1100000*β*z^4/17 - 750000*β*z^2/17 + 200000*β/51 + z^13 - 26*z^11 + 14300*z^9/57 - 357500*z^7/323 + 715000*z^5/323 - 550000*z^3/323 + 100000*z/323) ∧
    (derivative^[9] p).eval z = 106661318400 * (34295000*β^4/221 - 39710000*β^3*z^3/221 + 72200000*β^3*z/221 + 219450*β^2*z^6/17 - 1567500*β^2*z^4/17 + 31350000*β^2*z^2/221 - 5700000*β^2/221 - 220*β*z^9 + 52800*β*z^7/17 - 231000*β*z^5/17 + 4400000*β*z^3/221 - 1500000*β*z/221 + z^12 - 22*z^10 + 3300*z^8/19 - 192500*z^6/323 + 275000*z^4/323 - 1650000*z^2/4199 + 100000/4199) ∧
    (derivative^[10] p).eval z = 1279935820800 * (-9927500*β^3*z^2/221 + 18050000*β^3/663 + 109725*β^2*z^5/17 - 522500*β^2*z^3/17 + 5225000*β^2*z/221 - 165*β*z^8 + 30800*β*z^6/17 - 96250*β*z^4/17 + 1100000*β*z^2/221 - 125000*β/221 + z^11 - 55*z^9/3 + 2200*z^7/19 - 96250*z^5/323 + 275000*z^3/969 - 275000*z/4199) ∧
    (derivative^[11] p).eval z = 14079294028800 * (-1805000*β^3*z/221 + 49875*β^2*z^4/17 - 142500*β^2*z^2/17 + 475000*β^2/221 - 120*β*z^7 + 16800*β*z^5/17 - 35000*β*z^3/17 + 200000*β*z/221 + z^10 - 15*z^8 + 1400*z^6/19 - 43750*z^4/323 + 25000*z^2/323 - 25000/4199) ∧
    (derivative^[12] p).eval z = 140792940288000 * (-180500*β^3/221 + 19950*β^2*z^3/17 - 28500*β^2*z/17 - 84*β*z^6 + 8400*β*z^4/17 - 10500*β*z^2/17 + 20000*β/221 + z^9 - 12*z^7 + 840*z^5/19 - 17500*z^3/323 + 5000*z/323) ∧
    (derivative^[13] p).eval z = 1267136462592000 * (6650*β^2*z^2/17 - 9500*β^2/51 - 56*β*z^5 + 11200*β*z^3/51 - 7000*β*z/51 + z^8 - 28*z^6/3 + 1400*z^4/57 - 17500*z^2/969 + 5000/2907) ∧
    (derivative^[14] p).eval z = 10137091700736000 * (3325*β^2*z/34 - 35*β*z^4 + 1400*β*z^2/17 - 875*β/51 + z^7 - 7*z^5 + 700*z^3/57 - 4375*z/969) ∧
    (derivative^[15] p).eval z = 70959641905152000 * (475*β^2/34 - 20*β*z^3 + 400*β*z/17 + z^6 - 5*z^4 + 100*z^2/19 - 625/969) ∧
    (derivative^[16] p).eval z = 425757851430912000 * (-10*β*z^2 + 200*β/51 + z^5 - 10*z^3/3 + 100*z/57) ∧
    (derivative^[17] p).eval z = 2128789257154560000 * (-4*β*z + z^4 - 2*z^2 + 20/57) ∧
    (derivative^[18] p).eval z = 8515157028618240000 * (-β + z^3 - z) ∧
    (derivative^[19] p).eval z = 25545471085854720000 * (z^2 - 1/3) ∧
    (derivative^[20] p).eval z = 51090942171709440000 * (z) := by
  let p : Polynomial ℂ := (X^3-C (10)*X-190*C β)^7
  have hexpand := normalized_seventh_power_expansion β
  change p = _ at hexpand
  dsimp only
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  all_goals change (derivative^[_] p).eval z = _
  all_goals rw [hexpand]
  all_goals simp only [iterate_map_add,iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul,eval_add,eval_mul,eval_C,eval_pow,eval_X]
  all_goals norm_num [Nat.descFactorial] <;> ring
