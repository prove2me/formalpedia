-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cube_actual_row_values
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:00:51.719989+00:00
-- url     : https://prove2.me/submissions/bfe451cb-6d52-4044-bb5f-40351fafc645

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cubic_cube_expansion (β : ℂ) :
    (X^3-4*X-28*C β)^3 =
      C 1*X^9+C (-12)*X^7+C (-84*β)*X^6+C 48*X^5+C (672*β)*X^4+
      C (2352*β^2-64)*X^3+C (-1344*β)*X^2+C (-9408*β^2)*X^1+
      C (-21952*β^3)*X^0 := by
  simp only [C_sub,C_mul,C_pow,C_neg,C_ofNat]
  norm_num
  ring



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



open DerivativeChainPrivate in
theorem solution (β z : ℂ) :
    let p : Polynomial ℂ := (X ^ 3 - 4 * X - 28 * C β) ^ 3
    (derivative^[3] p).eval z = 504 *
      (z ^ 6 - 5 * z ^ 4 - 20 * β * z ^ 3 + 40/7 * z ^ 2 + 32 * β * z - 16/21 + 28 * β ^ 2) ∧
    (derivative^[4] p).eval z = 3024 *
      (z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β) ∧
    (derivative^[5] p).eval z = 15120 * (z ^ 4 - 2 * z ^ 2 - 4 * β * z + 8/21) ∧
    (derivative^[6] p).eval z = 60480 * (z ^ 3 - z - β) ∧
    (derivative^[7] p).eval z = 60480 * (3 * z ^ 2 - 1) ∧
    (derivative^[8] p).eval z = 362880 * z := by
  let p : Polynomial ℂ := (X ^ 3 - 4 * X - 28 * C β) ^ 3
  have hexpand := normalized_cubic_cube_expansion β
  change p = _ at hexpand
  have heval (k : ℕ) : (derivative^[k] p).eval z =
      (9 : ℕ).descFactorial k * z ^ (9-k) - 12 * (7 : ℕ).descFactorial k * z ^ (7-k) -
      84 * β * (6 : ℕ).descFactorial k * z ^ (6-k) +
      48 * (5 : ℕ).descFactorial k * z ^ (5-k) +
      672 * β * (4 : ℕ).descFactorial k * z ^ (4-k) +
      (2352 * β ^ 2 - 64) * (3 : ℕ).descFactorial k * z ^ (3-k) -
      1344 * β * (2 : ℕ).descFactorial k * z ^ (2-k) -
      9408 * β ^ 2 * (1 : ℕ).descFactorial k * z ^ (1-k) -
      21952 * β ^ 3 * (0 : ℕ).descFactorial k * z ^ (0-k) := by
    rw [hexpand]
    simp only [iterate_map_add derivative k,iterate_derivative_C_mul,
      iterate_derivative_X_pow_eq_C_mul,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    ring
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> change (derivative^[_] p).eval z = _
  all_goals rw [heval]; norm_num [Nat.descFactorial] <;> ring
