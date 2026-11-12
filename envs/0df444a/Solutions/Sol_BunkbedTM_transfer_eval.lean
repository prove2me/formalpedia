-- Prove2me | solution 1 for BunkbedTM.transfer_eval
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T16:06:11.965997+00:00
-- url     : https://prove2.me/submissions/7045bd23-fdd4-40c6-9345-b49f90df6309

import Definitions.Def_BunkbedTransferTables

/-!
# Evaluating the transfer matrix

The six-step transfer matrix is evaluated one hyperedge at a time. `stg k` says that summing
over the first `k` hyperedges, weighted by the WZ probabilities, collapses onto the `|layer k|`
reachable states with explicit polynomial weights; `q k` are the polynomial identities driving
one step, and `tr k` the state transitions. Sizes: 1, 5, 13, 34, 41, 41, 47 states.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

open Bunkbed Bunkbed.Hyper Bunkbed.TM Finset

namespace BunkbedTM

/-- Expand a sum over the five WZ states. -/
private theorem sum_wz (f : WZ → ℚ) :
    ∑ t : WZ, f t = f .abc + f .ab_c + f .ac_b + f .a_bc + f .a_b_c := by
  show ∑ t ∈ ({WZ.abc, WZ.ab_c, WZ.ac_b, WZ.a_bc, WZ.a_b_c} : Finset WZ), f t = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ## The weight tables of the six intermediate layers

Long chains of monomial summands elaborate superlinearly, so each table entry past 16
monomials is written as a sum of short `_p` pieces. -/
private def v0_0 (x y z u : Rat) : Rat := 1
private def v1_0 (x y z u : Rat) : Rat := x
private def v1_1 (x y z u : Rat) : Rat := y
private def v1_2 (x y z u : Rat) : Rat := z
private def v1_3 (x y z u : Rat) : Rat := u
private def v1_4 (x y z u : Rat) : Rat := u
private def v2_0 (x y z u : Rat) : Rat := x ^ 2
private def v2_1 (x y z u : Rat) : Rat := x * y + y * u + z * u + u ^ 2
private def v2_2 (x y z u : Rat) : Rat := x * z
private def v2_3 (x y z u : Rat) : Rat := x * u
private def v2_4 (x y z u : Rat) : Rat := 2 * x * u + u ^ 2
private def v2_5 (x y z u : Rat) : Rat := x * y + y * u + z * u + u ^ 2
private def v2_6 (x y z u : Rat) : Rat := y ^ 2 + 2 * y * z + 2 * y * u
private def v2_7 (x y z u : Rat) : Rat := x * z
private def v2_8 (x y z u : Rat) : Rat := z ^ 2
private def v2_9 (x y z u : Rat) : Rat := z * u
private def v2_10 (x y z u : Rat) : Rat := x * u
private def v2_11 (x y z u : Rat) : Rat := z * u
private def v2_12 (x y z u : Rat) : Rat := u ^ 2
private def v3_0 (x y z u : Rat) : Rat := x ^ 3
private def v3_1 (x y z u : Rat) : Rat := x ^ 2 * y + x * y * u + x * z * u + x * u ^ 2
private def v3_2 (x y z u : Rat) : Rat := x ^ 2 * z
private def v3_3 (x y z u : Rat) : Rat := x ^ 2 * u
private def v3_4 (x y z u : Rat) : Rat := 2 * x ^ 2 * u + x * u ^ 2
private def v3_5 (x y z u : Rat) : Rat := x ^ 2 * y + 2 * x * y * u + 2 * x * z * u + 3 * x * u ^ 2 + y * u ^ 2 + z * u ^ 2 + 2 * u ^ 3
private def v3_6 (x y z u : Rat) : Rat := x * y ^ 2 + 2 * x * y * z + 3 * x * y * u + y ^ 2 * u + 2 * y * z * u + z ^ 2 * u + 3 * y * u ^ 2 + 2 * z * u ^ 2 + u ^ 3
private def v3_7 (x y z u : Rat) : Rat := x ^ 2 * z
private def v3_8 (x y z u : Rat) : Rat := x * z ^ 2
private def v3_9 (x y z u : Rat) : Rat := x * z * u
private def v3_10 (x y z u : Rat) : Rat := 2 * x ^ 2 * u + x * u ^ 2
private def v3_11 (x y z u : Rat) : Rat := 2 * x * z * u + z * u ^ 2
private def v3_12 (x y z u : Rat) : Rat := 2 * x * u ^ 2 + u ^ 3
private def v3_13 (x y z u : Rat) : Rat := x ^ 2 * y + x * y * u + x * z * u + x * u ^ 2
private def v3_14 (x y z u : Rat) : Rat := x * y ^ 2 + y ^ 3 + 3 * y ^ 2 * z + 3 * y * z ^ 2 + 4 * y ^ 2 * u + 6 * y * z * u + 3 * y * u ^ 2
private def v3_15 (x y z u : Rat) : Rat := x * y * z + y * z * u + z ^ 2 * u + z * u ^ 2
private def v3_16 (x y z u : Rat) : Rat := x * y * u + y * u ^ 2 + z * u ^ 2 + u ^ 3
private def v3_17 (x y z u : Rat) : Rat := x * y ^ 2 + 2 * x * y * z + 3 * x * y * u + y ^ 2 * u + 2 * y * z * u + z ^ 2 * u + 3 * y * u ^ 2 + 2 * z * u ^ 2 + u ^ 3
private def v3_18 (x y z u : Rat) : Rat := x ^ 2 * z
private def v3_19 (x y z u : Rat) : Rat := x * y * z + y * z * u + z ^ 2 * u + z * u ^ 2
private def v3_20 (x y z u : Rat) : Rat := x * z ^ 2
private def v3_21 (x y z u : Rat) : Rat := x * z * u
private def v3_22 (x y z u : Rat) : Rat := 2 * x * z * u + z * u ^ 2
private def v3_23 (x y z u : Rat) : Rat := x * z ^ 2
private def v3_24 (x y z u : Rat) : Rat := z ^ 3
private def v3_25 (x y z u : Rat) : Rat := z ^ 2 * u
private def v3_26 (x y z u : Rat) : Rat := x ^ 2 * u
private def v3_27 (x y z u : Rat) : Rat := x * y * u + y * u ^ 2 + z * u ^ 2 + u ^ 3
private def v3_28 (x y z u : Rat) : Rat := x * z * u
private def v3_29 (x y z u : Rat) : Rat := x * u ^ 2
private def v3_30 (x y z u : Rat) : Rat := 2 * x * u ^ 2 + u ^ 3
private def v3_31 (x y z u : Rat) : Rat := x * z * u
private def v3_32 (x y z u : Rat) : Rat := z ^ 2 * u
private def v3_33 (x y z u : Rat) : Rat := z * u ^ 2
private def v4_0 (x y z u : Rat) : Rat := x ^ 4 + 2 * x ^ 3 * z + 6 * x ^ 3 * u + 3 * x ^ 2 * u ^ 2
private def v4_1 (x y z u : Rat) : Rat := x ^ 3 * y + x ^ 3 * u + x ^ 2 * y * u + 2 * x ^ 2 * z * u + 5 * x ^ 2 * u ^ 2 + 2 * x * u ^ 3
private def v4_2 (x y z u : Rat) : Rat := x ^ 3 * y + x ^ 3 * z + 2 * x ^ 2 * z ^ 2 + 2 * x ^ 2 * y * u + 4 * x ^ 2 * z * u + 3 * x ^ 2 * u ^ 2 + x * y * u ^ 2 + 2 * x * z * u ^ 2 + 2 * x * u ^ 3
private def v4_3 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 + 2 * x ^ 2 * y * z + 3 * x ^ 2 * y * u + x * y ^ 2 * u + x ^ 2 * z * u + 2 * x * y * z * u + 2 * x * z ^ 2 * u + 3 * x * y * u ^ 2 + 4 * x * z * u ^ 2 + x * u ^ 3 + z * u ^ 3
private def v4_4 (x y z u : Rat) : Rat := 2 * x ^ 2 * z * u + x * z * u ^ 2
private def v4_5 (x y z u : Rat) : Rat := x ^ 3 * y + x ^ 3 * z + 2 * x ^ 2 * z ^ 2 + 2 * x ^ 2 * y * u + 4 * x ^ 2 * z * u + 3 * x ^ 2 * u ^ 2 + x * y * u ^ 2 + 2 * x * z * u ^ 2 + 2 * x * u ^ 3
private def v4_6_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 + x * y ^ 3 + 3 * x * y ^ 2 * z + 3 * x * y * z ^ 2 + 6 * x * y ^ 2 * u + y ^ 3 * u + 9 * x * y * z * u + 3 * y ^ 2 * z * u + x * z ^ 2 * u + 3 * y * z ^ 2 * u + 2 * z ^ 3 * u + 6 * x * y * u ^ 2 + 5 * y ^ 2 * u ^ 2 + 9 * y * z * u ^ 2
private def v4_6_p1 (x y z u : Rat) : Rat := 3 * z ^ 2 * u ^ 2 + 6 * y * u ^ 3 + 3 * z * u ^ 3 + u ^ 4
private def v4_6 (x y z u : Rat) : Rat := v4_6_p0 x y z u + v4_6_p1 x y z u
private def v4_7 (x y z u : Rat) : Rat := x ^ 2 * y * z + 2 * x * y * z * u + 2 * x * z ^ 2 * u + 3 * x * z * u ^ 2 + y * z * u ^ 2 + z ^ 2 * u ^ 2 + 2 * z * u ^ 3
private def v4_8 (x y z u : Rat) : Rat := x ^ 2 * y * z + x ^ 2 * y * u + x ^ 2 * z * u + x * y * z * u + 2 * x * z ^ 2 * u + 2 * x * y * u ^ 2 + 3 * x * z * u ^ 2 + 3 * x * u ^ 3 + y * u ^ 3 + z * u ^ 3 + 2 * u ^ 4
private def v4_9_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 + 2 * x ^ 2 * y * z + x ^ 2 * z ^ 2 + 2 * x * z ^ 3 + 4 * x ^ 2 * y * u + 2 * x * y ^ 2 * u + 4 * x * y * z * u + 2 * x * z ^ 2 * u + 8 * x * y * u ^ 2 + y ^ 2 * u ^ 2 + 6 * x * z * u ^ 2 + 2 * y * z * u ^ 2 + z ^ 2 * u ^ 2 + 4 * x * u ^ 3
private def v4_9_p1 (x y z u : Rat) : Rat := 4 * y * u ^ 3 + 4 * z * u ^ 3 + 3 * u ^ 4
private def v4_9 (x y z u : Rat) : Rat := v4_9_p0 x y z u + v4_9_p1 x y z u
private def v4_10 (x y z u : Rat) : Rat := 2 * x ^ 2 * y * u + 3 * x * y * u ^ 2 + 2 * x * z * u ^ 2 + 2 * x * u ^ 3 + y * u ^ 3 + z * u ^ 3 + u ^ 4
private def v4_11 (x y z u : Rat) : Rat := 2 * x ^ 2 * z * u + x * z * u ^ 2
private def v4_12 (x y z u : Rat) : Rat := 4 * x ^ 2 * u ^ 2 + 4 * x * u ^ 3 + u ^ 4
private def v4_13 (x y z u : Rat) : Rat := 2 * x * z ^ 2 * u + z ^ 2 * u ^ 2
private def v4_14 (x y z u : Rat) : Rat := x ^ 3 * y + x ^ 3 * u + x ^ 2 * y * u + 2 * x ^ 2 * z * u + 5 * x ^ 2 * u ^ 2 + 2 * x * u ^ 3
private def v4_15 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 + 2 * x * y ^ 2 * u + 2 * x * y * z * u + 2 * x * y * u ^ 2 + y ^ 2 * u ^ 2 + 2 * y * z * u ^ 2 + z ^ 2 * u ^ 2 + 2 * y * u ^ 3 + 2 * z * u ^ 3 + u ^ 4
private def v4_16 (x y z u : Rat) : Rat := x ^ 2 * y * z + x * y * z * u + x * z ^ 2 * u + x * z * u ^ 2
private def v4_17 (x y z u : Rat) : Rat := 2 * x ^ 2 * y * u + x ^ 2 * u ^ 2 + 2 * x * y * u ^ 2 + 2 * x * z * u ^ 2 + 4 * x * u ^ 3 + u ^ 4
private def v4_18 (x y z u : Rat) : Rat := 2 * x ^ 2 * y * u + 3 * x * y * u ^ 2 + 2 * x * z * u ^ 2 + 2 * x * u ^ 3 + y * u ^ 3 + z * u ^ 3 + u ^ 4
private def v4_19_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 + x * y ^ 3 + 3 * x * y ^ 2 * z + 3 * x * y * z ^ 2 + 6 * x * y ^ 2 * u + y ^ 3 * u + 9 * x * y * z * u + 3 * y ^ 2 * z * u + x * z ^ 2 * u + 3 * y * z ^ 2 * u + 2 * z ^ 3 * u + 6 * x * y * u ^ 2 + 5 * y ^ 2 * u ^ 2 + 9 * y * z * u ^ 2
private def v4_19_p1 (x y z u : Rat) : Rat := 3 * z ^ 2 * u ^ 2 + 6 * y * u ^ 3 + 3 * z * u ^ 3 + u ^ 4
private def v4_19 (x y z u : Rat) : Rat := v4_19_p0 x y z u + v4_19_p1 x y z u
private def v4_20 (x y z u : Rat) : Rat := 2 * x * y ^ 3 + y ^ 4 + 4 * x * y ^ 2 * z + 4 * y ^ 3 * z + 6 * y ^ 2 * z ^ 2 + 4 * y * z ^ 3 + 4 * x * y ^ 2 * u + 6 * y ^ 3 * u + 16 * y ^ 2 * z * u + 12 * y * z ^ 2 * u + 10 * y ^ 2 * u ^ 2 + 12 * y * z * u ^ 2 + z ^ 2 * u ^ 2 + 4 * y * u ^ 3
private def v4_21 (x y z u : Rat) : Rat := x ^ 2 * y * z + x ^ 2 * y * u + x ^ 2 * z * u + x * y * z * u + 2 * x * z ^ 2 * u + 2 * x * y * u ^ 2 + 3 * x * z * u ^ 2 + 3 * x * u ^ 3 + y * u ^ 3 + z * u ^ 3 + 2 * u ^ 4
private def v4_22 (x y z u : Rat) : Rat := x * y * z ^ 2 + y * z ^ 2 * u + z ^ 3 * u + z ^ 2 * u ^ 2
private def v4_23 (x y z u : Rat) : Rat := x * y ^ 2 * u + 3 * x * y * z * u + 3 * x * y * u ^ 2 + y ^ 2 * u ^ 2 + x * z * u ^ 2 + 3 * y * z * u ^ 2 + 2 * z ^ 2 * u ^ 2 + 3 * y * u ^ 3 + 3 * z * u ^ 3 + u ^ 4
private def v4_24 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 + 2 * x ^ 2 * y * z + 3 * x ^ 2 * y * u + x * y ^ 2 * u + x ^ 2 * z * u + 2 * x * y * z * u + 2 * x * z ^ 2 * u + 3 * x * y * u ^ 2 + 4 * x * z * u ^ 2 + x * u ^ 3 + z * u ^ 3
private def v4_25 (x y z u : Rat) : Rat := x * y ^ 2 * z + 2 * x * y * z ^ 2 + 3 * x * y * z * u + y ^ 2 * z * u + 2 * y * z ^ 2 * u + z ^ 3 * u + 3 * y * z * u ^ 2 + 2 * z ^ 2 * u ^ 2 + z * u ^ 3
private def v4_26 (x y z u : Rat) : Rat := x * y ^ 2 * u + 3 * x * y * z * u + 3 * x * y * u ^ 2 + y ^ 2 * u ^ 2 + x * z * u ^ 2 + 3 * y * z * u ^ 2 + 2 * z ^ 2 * u ^ 2 + 3 * y * u ^ 3 + 3 * z * u ^ 3 + u ^ 4
private def v4_27 (x y z u : Rat) : Rat := x ^ 2 * y * z + x * y * z * u + x * z ^ 2 * u + x * z * u ^ 2
private def v4_28 (x y z u : Rat) : Rat := x ^ 2 * z ^ 2
private def v4_29 (x y z u : Rat) : Rat := 2 * x ^ 2 * z * u + x * z * u ^ 2
private def v4_30 (x y z u : Rat) : Rat := x ^ 2 * y * z + 2 * x * y * z * u + 2 * x * z ^ 2 * u + 3 * x * z * u ^ 2 + y * z * u ^ 2 + z ^ 2 * u ^ 2 + 2 * z * u ^ 3
private def v4_31 (x y z u : Rat) : Rat := x * y ^ 2 * z + 2 * x * y * z ^ 2 + 3 * x * y * z * u + y ^ 2 * z * u + 2 * y * z ^ 2 * u + z ^ 3 * u + 3 * y * z * u ^ 2 + 2 * z ^ 2 * u ^ 2 + z * u ^ 3
private def v4_32 (x y z u : Rat) : Rat := x * z ^ 3
private def v4_33 (x y z u : Rat) : Rat := 2 * x ^ 2 * z * u + x * z * u ^ 2
private def v4_34 (x y z u : Rat) : Rat := 2 * x * z ^ 2 * u + z ^ 2 * u ^ 2
private def v4_35 (x y z u : Rat) : Rat := 2 * x * z * u ^ 2 + z * u ^ 3
private def v4_36 (x y z u : Rat) : Rat := x * y * z ^ 2 + y * z ^ 2 * u + z ^ 3 * u + z ^ 2 * u ^ 2
private def v4_37 (x y z u : Rat) : Rat := x * z ^ 3
private def v4_38 (x y z u : Rat) : Rat := 2 * x * z ^ 2 * u + z ^ 2 * u ^ 2
private def v4_39 (x y z u : Rat) : Rat := z ^ 4
private def v4_40 (x y z u : Rat) : Rat := 2 * x * z * u ^ 2 + z * u ^ 3
private def v5_0 (x y z u : Rat) : Rat := x ^ 5 + 2 * x ^ 4 * y + 4 * x ^ 4 * z + 4 * x ^ 3 * z ^ 2 + 8 * x ^ 4 * u + 4 * x ^ 3 * y * u + 16 * x ^ 3 * z * u + 22 * x ^ 3 * u ^ 2 + 2 * x ^ 2 * y * u ^ 2 + 8 * x ^ 2 * z * u ^ 2 + 16 * x ^ 2 * u ^ 3 + 3 * x * u ^ 4
private def v5_1_p0 (x y z u : Rat) : Rat := x ^ 4 * y + x ^ 3 * y ^ 2 + 3 * x ^ 3 * y * z + x ^ 4 * u + 9 * x ^ 3 * y * u + x ^ 2 * y ^ 2 * u + 4 * x ^ 3 * z * u + 3 * x ^ 2 * y * z * u + 4 * x ^ 2 * z ^ 2 * u + 7 * x ^ 3 * u ^ 2 + 11 * x ^ 2 * y * u ^ 2 + 13 * x ^ 2 * z * u ^ 2 + 15 * x ^ 2 * u ^ 3 + 3 * x * y * u ^ 3
private def v5_1_p1 (x y z u : Rat) : Rat := 5 * x * z * u ^ 3 + 8 * x * u ^ 4 + u ^ 5
private def v5_1 (x y z u : Rat) : Rat := v5_1_p0 x y z u + v5_1_p1 x y z u
private def v5_2_p0 (x y z u : Rat) : Rat := x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x ^ 3 * y * z + 3 * x ^ 2 * y ^ 2 * z + 4 * x ^ 2 * y * z ^ 2 + 6 * x ^ 2 * y ^ 2 * u + x * y ^ 3 * u + 12 * x ^ 2 * y * z * u + 3 * x * y ^ 2 * z * u + x ^ 2 * z ^ 2 * u + 4 * x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 6 * x ^ 2 * y * u ^ 2 + 5 * x * y ^ 2 * u ^ 2
private def v5_2_p1 (x y z u : Rat) : Rat := 3 * x ^ 2 * z * u ^ 2 + 12 * x * y * z * u ^ 2 + 6 * x * z ^ 2 * u ^ 2 + 6 * x * y * u ^ 3 + 6 * x * z * u ^ 3 + y * z * u ^ 3 + z ^ 2 * u ^ 3 + x * u ^ 4 + z * u ^ 4
private def v5_2 (x y z u : Rat) : Rat := v5_2_p0 x y z u + v5_2_p1 x y z u
private def v5_3 (x y z u : Rat) : Rat := x ^ 3 * y * z + x ^ 3 * z ^ 2 + 2 * x ^ 2 * z ^ 3 + 2 * x ^ 2 * y * z * u + 4 * x ^ 2 * z ^ 2 * u + 3 * x ^ 2 * z * u ^ 2 + x * y * z * u ^ 2 + 2 * x * z ^ 2 * u ^ 2 + 2 * x * z * u ^ 3
private def v5_4_p0 (x y z u : Rat) : Rat := x ^ 3 * y ^ 2 + 2 * x ^ 3 * y * z + 4 * x ^ 3 * y * u + 2 * x ^ 2 * y ^ 2 * u + 4 * x ^ 3 * z * u + 4 * x ^ 2 * y * z * u + 6 * x ^ 2 * z ^ 2 * u + 8 * x ^ 2 * y * u ^ 2 + x * y ^ 2 * u ^ 2 + 12 * x ^ 2 * z * u ^ 2 + 2 * x * y * z * u ^ 2 + 3 * x * z ^ 2 * u ^ 2 + 4 * x ^ 2 * u ^ 3 + 4 * x * y * u ^ 3
private def v5_4_p1 (x y z u : Rat) : Rat := 8 * x * z * u ^ 3 + 3 * x * u ^ 4 + z * u ^ 4
private def v5_4 (x y z u : Rat) : Rat := v5_4_p0 x y z u + v5_4_p1 x y z u
private def v5_5_p0 (x y z u : Rat) : Rat := x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 4 * z + 4 * x ^ 3 * y * z + 4 * x ^ 3 * z ^ 2 + 4 * x ^ 2 * z ^ 3 + 8 * x ^ 3 * y * u + 2 * x ^ 2 * y ^ 2 * u + 6 * x ^ 3 * z * u + 8 * x ^ 2 * y * z * u + 12 * x ^ 2 * z ^ 2 * u + 3 * x ^ 3 * u ^ 2 + 14 * x ^ 2 * y * u ^ 2 + x * y ^ 2 * u ^ 2
private def v5_5_p1 (x y z u : Rat) : Rat := 19 * x ^ 2 * z * u ^ 2 + 4 * x * y * z * u ^ 2 + 6 * x * z ^ 2 * u ^ 2 + 12 * x ^ 2 * u ^ 3 + 8 * x * y * u ^ 3 + 12 * x * z * u ^ 3 + 10 * x * u ^ 4 + y * u ^ 4 + z * u ^ 4 + 2 * u ^ 5
private def v5_5 (x y z u : Rat) : Rat := v5_5_p0 x y z u + v5_5_p1 x y z u
private def v5_6_p0 (x y z u : Rat) : Rat := x ^ 3 * y ^ 2 + x ^ 3 * y * z + x ^ 2 * y ^ 2 * z + 3 * x ^ 2 * y * z ^ 2 + x ^ 3 * y * u + 4 * x ^ 2 * y ^ 2 * u + x ^ 3 * z * u + 9 * x ^ 2 * y * z * u + x * y ^ 2 * z * u + 4 * x ^ 2 * z ^ 2 * u + 3 * x * y * z ^ 2 * u + 4 * x * z ^ 3 * u + 10 * x ^ 2 * y * u ^ 2 + 5 * x * y ^ 2 * u ^ 2
private def v5_6_p1 (x y z u : Rat) : Rat := 5 * x ^ 2 * z * u ^ 2 + 12 * x * y * z * u ^ 2 + 9 * x * z ^ 2 * u ^ 2 + 3 * x ^ 2 * u ^ 3 + 16 * x * y * u ^ 3 + 2 * y ^ 2 * u ^ 3 + 14 * x * z * u ^ 3 + 4 * y * z * u ^ 3 + 3 * z ^ 2 * u ^ 3 + 9 * x * u ^ 4 + 7 * y * u ^ 4 + 7 * z * u ^ 4 + 5 * u ^ 5
private def v5_6 (x y z u : Rat) : Rat := v5_6_p0 x y z u + v5_6_p1 x y z u
private def v5_7_p0 (x y z u : Rat) : Rat := x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x ^ 3 * y * z + 3 * x ^ 2 * y ^ 2 * z + 4 * x ^ 2 * y * z ^ 2 + 8 * x ^ 2 * y ^ 2 * u + 2 * x * y ^ 3 * u + 14 * x ^ 2 * y * z * u + 6 * x * y ^ 2 * z * u + 4 * x ^ 2 * z ^ 2 * u + 8 * x * y * z ^ 2 * u + 6 * x * z ^ 3 * u + 10 * x ^ 2 * y * u ^ 2 + 13 * x * y ^ 2 * u ^ 2
private def v5_7_p1 (x y z u : Rat) : Rat := y ^ 3 * u ^ 2 + 3 * x ^ 2 * z * u ^ 2 + 25 * x * y * z * u ^ 2 + 3 * y ^ 2 * z * u ^ 2 + 14 * x * z ^ 2 * u ^ 2 + 4 * y * z ^ 2 * u ^ 2 + 3 * z ^ 3 * u ^ 2 + 20 * x * y * u ^ 3 + 6 * y ^ 2 * u ^ 3 + 14 * x * z * u ^ 3 + 12 * y * z * u ^ 3 + 8 * z ^ 2 * u ^ 3 + 5 * x * u ^ 4 + 10 * y * u ^ 4
private def v5_7_p2 (x y z u : Rat) : Rat := 9 * z * u ^ 4 + 4 * u ^ 5
private def v5_7 (x y z u : Rat) : Rat := v5_7_p0 x y z u + v5_7_p1 x y z u + v5_7_p2 x y z u
private def v5_8_p0 (x y z u : Rat) : Rat := 2 * x ^ 2 * y ^ 3 + x * y ^ 4 + 4 * x ^ 2 * y ^ 2 * z + 4 * x * y ^ 3 * z + x ^ 2 * y * z ^ 2 + 6 * x * y ^ 2 * z ^ 2 + 5 * x * y * z ^ 3 + 5 * x ^ 2 * y ^ 2 * u + 9 * x * y ^ 3 * u + y ^ 4 * u + x ^ 2 * y * z * u + 24 * x * y ^ 2 * z * u + 4 * y ^ 3 * z * u + 19 * x * y * z ^ 2 * u
private def v5_8_p1 (x y z u : Rat) : Rat := 6 * y ^ 2 * z ^ 2 * u + x * z ^ 3 * u + 5 * y * z ^ 3 * u + 2 * z ^ 4 * u + 20 * x * y ^ 2 * u ^ 2 + 7 * y ^ 3 * u ^ 2 + 26 * x * y * z * u ^ 2 + 20 * y ^ 2 * z * u ^ 2 + 3 * x * z ^ 2 * u ^ 2 + 18 * y * z ^ 2 * u ^ 2 + 5 * z ^ 3 * u ^ 2 + 10 * x * y * u ^ 3 + 15 * y ^ 2 * u ^ 3 + 3 * x * z * u ^ 3
private def v5_8_p2 (x y z u : Rat) : Rat := 25 * y * z * u ^ 3 + 7 * z ^ 2 * u ^ 3 + 10 * y * u ^ 4 + 6 * z * u ^ 4 + u ^ 5
private def v5_8 (x y z u : Rat) : Rat := v5_8_p0 x y z u + v5_8_p1 x y z u + v5_8_p2 x y z u
private def v5_9_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * z + 2 * x ^ 2 * y * z ^ 2 + x ^ 2 * z ^ 3 + 2 * x * z ^ 4 + 4 * x ^ 2 * y * z * u + 2 * x * y ^ 2 * z * u + 4 * x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 8 * x * y * z * u ^ 2 + y ^ 2 * z * u ^ 2 + 6 * x * z ^ 2 * u ^ 2 + 2 * y * z ^ 2 * u ^ 2 + z ^ 3 * u ^ 2 + 4 * x * z * u ^ 3
private def v5_9_p1 (x y z u : Rat) : Rat := 4 * y * z * u ^ 3 + 4 * z ^ 2 * u ^ 3 + 3 * z * u ^ 4
private def v5_9 (x y z u : Rat) : Rat := v5_9_p0 x y z u + v5_9_p1 x y z u
private def v5_10 (x y z u : Rat) : Rat := 2 * x ^ 3 * y * u + 2 * x ^ 3 * z * u + 4 * x ^ 2 * z ^ 2 * u + 5 * x ^ 2 * y * u ^ 2 + 5 * x ^ 2 * z * u ^ 2 + 2 * x * z ^ 2 * u ^ 2 + 6 * x ^ 2 * u ^ 3 + 4 * x * y * u ^ 3 + 4 * x * z * u ^ 3 + 7 * x * u ^ 4 + y * u ^ 4 + z * u ^ 4 + 2 * u ^ 5
private def v5_11 (x y z u : Rat) : Rat := 2 * x ^ 2 * y ^ 2 * u + 4 * x ^ 2 * y * z * u + 6 * x ^ 2 * y * u ^ 2 + 3 * x * y ^ 2 * u ^ 2 + 2 * x ^ 2 * z * u ^ 2 + 6 * x * y * z * u ^ 2 + 4 * x * z ^ 2 * u ^ 2 + 9 * x * y * u ^ 3 + y ^ 2 * u ^ 3 + 5 * x * z * u ^ 3 + 2 * y * z * u ^ 3 + 2 * z ^ 2 * u ^ 3 + 2 * x * u ^ 4 + 3 * y * u ^ 4 + 2 * z * u ^ 4 + u ^ 5
private def v5_12 (x y z u : Rat) : Rat := 4 * x ^ 2 * z * u ^ 2 + 4 * x * z * u ^ 3 + z * u ^ 4
private def v5_13 (x y z u : Rat) : Rat := 2 * x * z ^ 3 * u + z ^ 3 * u ^ 2
private def v5_14 (x y z u : Rat) : Rat := x ^ 4 * y + 2 * x ^ 3 * y * z + x ^ 4 * u + 7 * x ^ 3 * y * u + 4 * x ^ 3 * z * u + 2 * x ^ 2 * y * z * u + 4 * x ^ 2 * z ^ 2 * u + 7 * x ^ 3 * u ^ 2 + 10 * x ^ 2 * y * u ^ 2 + 14 * x ^ 2 * z * u ^ 2 + 17 * x ^ 2 * u ^ 3 + 4 * x * y * u ^ 3 + 6 * x * z * u ^ 3 + 10 * x * u ^ 4 + u ^ 5
private def v5_15_p0 (x y z u : Rat) : Rat := x ^ 3 * y ^ 2 + 2 * x ^ 3 * y * u + 3 * x ^ 2 * y ^ 2 * u + 5 * x ^ 2 * y * z * u + x ^ 3 * u ^ 2 + 12 * x ^ 2 * y * u ^ 2 + 2 * x * y ^ 2 * u ^ 2 + 4 * x ^ 2 * z * u ^ 2 + 5 * x * y * z * u ^ 2 + 4 * x * z ^ 2 * u ^ 2 + 6 * x ^ 2 * u ^ 3 + 13 * x * y * u ^ 3 + 11 * x * z * u ^ 3 + 11 * x * u ^ 4
private def v5_15_p1 (x y z u : Rat) : Rat := 3 * y * u ^ 4 + 3 * z * u ^ 4 + 4 * u ^ 5
private def v5_15 (x y z u : Rat) : Rat := v5_15_p0 x y z u + v5_15_p1 x y z u
private def v5_16_p0 (x y z u : Rat) : Rat := x ^ 3 * y ^ 2 + x ^ 3 * y * z + 2 * x ^ 2 * y * z ^ 2 + 3 * x ^ 2 * y ^ 2 * u + 4 * x ^ 2 * y * z * u + x ^ 2 * z ^ 2 * u + 2 * x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 4 * x ^ 2 * y * u ^ 2 + 3 * x * y ^ 2 * u ^ 2 + x ^ 2 * z * u ^ 2 + 5 * x * y * z * u ^ 2 + 4 * x * z ^ 2 * u ^ 2 + 7 * x * y * u ^ 3
private def v5_16_p1 (x y z u : Rat) : Rat := y ^ 2 * u ^ 3 + 5 * x * z * u ^ 3 + 2 * y * z * u ^ 3 + z ^ 2 * u ^ 3 + 3 * x * u ^ 4 + 3 * y * u ^ 4 + 3 * z * u ^ 4 + 2 * u ^ 5
private def v5_16 (x y z u : Rat) : Rat := v5_16_p0 x y z u + v5_16_p1 x y z u
private def v5_17_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 3 + 2 * x ^ 2 * y ^ 2 * z + 3 * x ^ 2 * y ^ 2 * u + 2 * x * y ^ 3 * u + x ^ 2 * y * z * u + 5 * x * y ^ 2 * z * u + 4 * x * y * z ^ 2 * u + 7 * x * y ^ 2 * u ^ 2 + y ^ 3 * u ^ 2 + 8 * x * y * z * u ^ 2 + 3 * y ^ 2 * z * u ^ 2 + x * z ^ 2 * u ^ 2 + 4 * y * z ^ 2 * u ^ 2 + 2 * z ^ 3 * u ^ 2
private def v5_17_p1 (x y z u : Rat) : Rat := 4 * x * y * u ^ 3 + 4 * y ^ 2 * u ^ 3 + x * z * u ^ 3 + 7 * y * z * u ^ 3 + 4 * z ^ 2 * u ^ 3 + 4 * y * u ^ 4 + 3 * z * u ^ 4 + u ^ 5
private def v5_17 (x y z u : Rat) : Rat := v5_17_p0 x y z u + v5_17_p1 x y z u
private def v5_18 (x y z u : Rat) : Rat := 2 * x ^ 2 * y * z * u + 3 * x * y * z * u ^ 2 + 2 * x * z ^ 2 * u ^ 2 + 2 * x * z * u ^ 3 + y * z * u ^ 3 + z ^ 2 * u ^ 3 + z * u ^ 4
private def v5_19_p0 (x y z u : Rat) : Rat := 2 * x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + 2 * x ^ 3 * y * z + 4 * x ^ 2 * y ^ 2 * z + 5 * x ^ 2 * y * z ^ 2 + 3 * x ^ 3 * y * u + 9 * x ^ 2 * y ^ 2 * u + x * y ^ 3 * u + x ^ 3 * z * u + 19 * x ^ 2 * y * z * u + 4 * x * y ^ 2 * z * u + 4 * x ^ 2 * z ^ 2 * u + 5 * x * y * z ^ 2 * u + 4 * x * z ^ 3 * u
private def v5_19_p1 (x y z u : Rat) : Rat := 15 * x ^ 2 * y * u ^ 2 + 8 * x * y ^ 2 * u ^ 2 + 6 * x ^ 2 * z * u ^ 2 + 20 * x * y * z * u ^ 2 + 11 * x * z ^ 2 * u ^ 2 + x ^ 2 * u ^ 3 + 15 * x * y * u ^ 3 + y ^ 2 * u ^ 3 + 13 * x * z * u ^ 3 + 3 * y * z * u ^ 3 + 3 * z ^ 2 * u ^ 3 + 3 * x * u ^ 4 + 3 * y * u ^ 4 + 4 * z * u ^ 4
private def v5_19_p2 (x y z u : Rat) : Rat := u ^ 5
private def v5_19 (x y z u : Rat) : Rat := v5_19_p0 x y z u + v5_19_p1 x y z u + v5_19_p2 x y z u
private def v5_20_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 3 + 3 * x * y ^ 4 + y ^ 5 + 10 * x * y ^ 3 * z + 5 * y ^ 4 * z + 10 * x * y ^ 2 * z ^ 2 + 10 * y ^ 3 * z ^ 2 + 10 * y ^ 2 * z ^ 3 + 5 * y * z ^ 4 + 12 * x * y ^ 3 * u + 8 * y ^ 4 * u + 21 * x * y ^ 2 * z * u + 30 * y ^ 3 * z * u + 3 * x * y * z ^ 2 * u
private def v5_20_p1 (x y z u : Rat) : Rat := 40 * y ^ 2 * z ^ 2 * u + 20 * y * z ^ 3 * u + 10 * x * y ^ 2 * u ^ 2 + 21 * y ^ 3 * u ^ 2 + 3 * x * y * z * u ^ 2 + 51 * y ^ 2 * z * u ^ 2 + 33 * y * z ^ 2 * u ^ 2 + 2 * z ^ 3 * u ^ 2 + 20 * y ^ 2 * u ^ 3 + 23 * y * z * u ^ 3 + 3 * z ^ 2 * u ^ 3 + 5 * y * u ^ 4 + z * u ^ 4
private def v5_20 (x y z u : Rat) : Rat := v5_20_p0 x y z u + v5_20_p1 x y z u
private def v5_21_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * z + x * y ^ 3 * z + 3 * x * y ^ 2 * z ^ 2 + 3 * x * y * z ^ 3 + 6 * x * y ^ 2 * z * u + y ^ 3 * z * u + 9 * x * y * z ^ 2 * u + 3 * y ^ 2 * z ^ 2 * u + x * z ^ 3 * u + 3 * y * z ^ 3 * u + 2 * z ^ 4 * u + 6 * x * y * z * u ^ 2 + 5 * y ^ 2 * z * u ^ 2 + 9 * y * z ^ 2 * u ^ 2
private def v5_21_p1 (x y z u : Rat) : Rat := 3 * z ^ 3 * u ^ 2 + 6 * y * z * u ^ 3 + 3 * z ^ 2 * u ^ 3 + z * u ^ 4
private def v5_21 (x y z u : Rat) : Rat := v5_21_p0 x y z u + v5_21_p1 x y z u
private def v5_22_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 3 + 2 * x ^ 2 * y ^ 2 * z + 5 * x ^ 2 * y ^ 2 * u + 3 * x * y ^ 3 * u + 3 * x ^ 2 * y * z * u + 9 * x * y ^ 2 * z * u + 8 * x * y * z ^ 2 * u + 3 * x ^ 2 * y * u ^ 2 + 14 * x * y ^ 2 * u ^ 2 + 2 * y ^ 3 * u ^ 2 + x ^ 2 * z * u ^ 2 + 22 * x * y * z * u ^ 2 + 7 * y ^ 2 * z * u ^ 2 + 4 * x * z ^ 2 * u ^ 2
private def v5_22_p1 (x y z u : Rat) : Rat := 8 * y * z ^ 2 * u ^ 2 + 4 * z ^ 3 * u ^ 2 + 13 * x * y * u ^ 3 + 9 * y ^ 2 * u ^ 3 + 5 * x * z * u ^ 3 + 19 * y * z * u ^ 3 + 8 * z ^ 2 * u ^ 3 + x * u ^ 4 + 10 * y * u ^ 4 + 8 * z * u ^ 4 + 2 * u ^ 5
private def v5_22 (x y z u : Rat) : Rat := v5_22_p0 x y z u + v5_22_p1 x y z u
private def v5_23_p0 (x y z u : Rat) : Rat := 2 * x ^ 2 * y ^ 3 + x * y ^ 4 + 5 * x ^ 2 * y ^ 2 * z + 4 * x * y ^ 3 * z + 2 * x ^ 2 * y * z ^ 2 + 7 * x * y ^ 2 * z ^ 2 + 6 * x * y * z ^ 3 + 5 * x ^ 2 * y ^ 2 * u + 9 * x * y ^ 3 * u + y ^ 4 * u + 3 * x ^ 2 * y * z * u + 25 * x * y ^ 2 * z * u + 4 * y ^ 3 * z * u + 23 * x * y * z ^ 2 * u
private def v5_23_p1 (x y z u : Rat) : Rat := 7 * y ^ 2 * z ^ 2 * u + x * z ^ 3 * u + 6 * y * z ^ 3 * u + 2 * z ^ 4 * u + 20 * x * y ^ 2 * u ^ 2 + 7 * y ^ 3 * u ^ 2 + 27 * x * y * z * u ^ 2 + 20 * y ^ 2 * z * u ^ 2 + 4 * x * z ^ 2 * u ^ 2 + 21 * y * z ^ 2 * u ^ 2 + 6 * z ^ 3 * u ^ 2 + 10 * x * y * u ^ 3 + 15 * y ^ 2 * u ^ 3 + x * z * u ^ 3
private def v5_23_p2 (x y z u : Rat) : Rat := 24 * y * z * u ^ 3 + 8 * z ^ 2 * u ^ 3 + 10 * y * u ^ 4 + 4 * z * u ^ 4 + u ^ 5
private def v5_23 (x y z u : Rat) : Rat := v5_23_p0 x y z u + v5_23_p1 x y z u + v5_23_p2 x y z u
private def v5_24_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * z + x ^ 2 * y ^ 2 * u + x * y ^ 3 * u + x ^ 2 * y * z * u + 5 * x * y ^ 2 * z * u + 5 * x * y * z ^ 2 * u + 6 * x * y ^ 2 * u ^ 2 + y ^ 3 * u ^ 2 + 12 * x * y * z * u ^ 2 + 4 * y ^ 2 * z * u ^ 2 + x * z ^ 2 * u ^ 2 + 5 * y * z ^ 2 * u ^ 2 + 2 * z ^ 3 * u ^ 2 + 6 * x * y * u ^ 3
private def v5_24_p1 (x y z u : Rat) : Rat := 5 * y ^ 2 * u ^ 3 + 3 * x * z * u ^ 3 + 11 * y * z * u ^ 3 + 5 * z ^ 2 * u ^ 3 + 6 * y * u ^ 4 + 5 * z * u ^ 4 + u ^ 5
private def v5_24 (x y z u : Rat) : Rat := v5_24_p0 x y z u + v5_24_p1 x y z u
private def v5_25 (x y z u : Rat) : Rat := x ^ 2 * y * z ^ 2 + x ^ 2 * y * z * u + x ^ 2 * z ^ 2 * u + x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 2 * x * y * z * u ^ 2 + 3 * x * z ^ 2 * u ^ 2 + 3 * x * z * u ^ 3 + y * z * u ^ 3 + z ^ 2 * u ^ 3 + 2 * z * u ^ 4
private def v5_26 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * u + 4 * x ^ 2 * y * z * u + 4 * x ^ 2 * y * u ^ 2 + 2 * x * y ^ 2 * u ^ 2 + 4 * x ^ 2 * z * u ^ 2 + 7 * x * y * z * u ^ 2 + 6 * x * z ^ 2 * u ^ 2 + 8 * x * y * u ^ 3 + y ^ 2 * u ^ 3 + 10 * x * z * u ^ 3 + 3 * y * z * u ^ 3 + 3 * z ^ 2 * u ^ 3 + 4 * x * u ^ 4 + 4 * y * u ^ 4 + 5 * z * u ^ 4 + 3 * u ^ 5
private def v5_27 (x y z u : Rat) : Rat := x * y * z ^ 3 + y * z ^ 3 * u + z ^ 4 * u + z ^ 3 * u ^ 2
private def v5_28 (x y z u : Rat) : Rat := x ^ 3 * y * z + x ^ 3 * z ^ 2 + 2 * x ^ 2 * z ^ 3 + 2 * x ^ 2 * y * z * u + 2 * x ^ 2 * z ^ 2 * u + 3 * x ^ 2 * z * u ^ 2 + x * y * z * u ^ 2 + x * z ^ 2 * u ^ 2 + 2 * x * z * u ^ 3
private def v5_29 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * z + 2 * x ^ 2 * y * z ^ 2 + 3 * x ^ 2 * y * z * u + x * y ^ 2 * z * u + x ^ 2 * z ^ 2 * u + 2 * x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 3 * x * y * z * u ^ 2 + 2 * x * z ^ 2 * u ^ 2 + x * z * u ^ 3
private def v5_30 (x y z u : Rat) : Rat := 2 * x ^ 2 * z ^ 2 * u + x * z ^ 2 * u ^ 2
private def v5_31 (x y z u : Rat) : Rat := x ^ 3 * y * z + 2 * x ^ 3 * z * u + 2 * x ^ 2 * y * z * u + 4 * x ^ 2 * z ^ 2 * u + 8 * x ^ 2 * z * u ^ 2 + x * y * z * u ^ 2 + 2 * x * z ^ 2 * u ^ 2 + 6 * x * z * u ^ 3 + z * u ^ 4
private def v5_32_p0 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * z + x * y ^ 3 * z + 3 * x * y ^ 2 * z ^ 2 + 3 * x * y * z ^ 3 + 6 * x * y ^ 2 * z * u + y ^ 3 * z * u + 9 * x * y * z ^ 2 * u + 3 * y ^ 2 * z ^ 2 * u + 3 * y * z ^ 3 * u + z ^ 4 * u + 6 * x * y * z * u ^ 2 + 5 * y ^ 2 * z * u ^ 2 + 2 * x * z ^ 2 * u ^ 2 + 9 * y * z ^ 2 * u ^ 2
private def v5_32_p1 (x y z u : Rat) : Rat := 3 * z ^ 3 * u ^ 2 + 6 * y * z * u ^ 3 + 4 * z ^ 2 * u ^ 3 + z * u ^ 4
private def v5_32 (x y z u : Rat) : Rat := v5_32_p0 x y z u + v5_32_p1 x y z u
private def v5_33 (x y z u : Rat) : Rat := x ^ 2 * y * z ^ 2 + 2 * x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 3 * x * z ^ 2 * u ^ 2 + y * z ^ 2 * u ^ 2 + z ^ 3 * u ^ 2 + 2 * z ^ 2 * u ^ 3
private def v5_34 (x y z u : Rat) : Rat := 3 * x ^ 2 * y * z * u + 2 * x ^ 2 * z * u ^ 2 + 5 * x * y * z * u ^ 2 + 4 * x * z ^ 2 * u ^ 2 + 6 * x * z * u ^ 3 + 2 * y * z * u ^ 3 + 2 * z ^ 2 * u ^ 3 + 3 * z * u ^ 4
private def v5_35 (x y z u : Rat) : Rat := x ^ 2 * y ^ 2 * z + 2 * x ^ 2 * y * z ^ 2 + 4 * x ^ 2 * y * z * u + 2 * x * y ^ 2 * z * u + 2 * x ^ 2 * z ^ 2 * u + 4 * x * y * z ^ 2 * u + 4 * x * z ^ 3 * u + 8 * x * y * z * u ^ 2 + y ^ 2 * z * u ^ 2 + 7 * x * z ^ 2 * u ^ 2 + 2 * y * z ^ 2 * u ^ 2 + 2 * z ^ 3 * u ^ 2 + 4 * x * z * u ^ 3 + 4 * y * z * u ^ 3 + 4 * z ^ 2 * u ^ 3 + 3 * z * u ^ 4
private def v5_36 (x y z u : Rat) : Rat := x * z ^ 4
private def v5_37 (x y z u : Rat) : Rat := x ^ 2 * y * z ^ 2 + x ^ 2 * z ^ 3 + 2 * x * z ^ 4 + 2 * x * y * z ^ 2 * u + 2 * x * z ^ 3 * u + 3 * x * z ^ 2 * u ^ 2 + y * z ^ 2 * u ^ 2 + z ^ 3 * u ^ 2 + 2 * z ^ 2 * u ^ 3
private def v5_38 (x y z u : Rat) : Rat := x * y ^ 2 * z ^ 2 + 2 * x * y * z ^ 3 + 3 * x * y * z ^ 2 * u + y ^ 2 * z ^ 2 * u + x * z ^ 3 * u + 2 * y * z ^ 3 * u + 2 * z ^ 4 * u + 3 * y * z ^ 2 * u ^ 2 + 2 * z ^ 3 * u ^ 2 + z ^ 2 * u ^ 3
private def v5_39 (x y z u : Rat) : Rat := 2 * x * z ^ 3 * u + z ^ 3 * u ^ 2
private def v5_40 (x y z u : Rat) : Rat := z ^ 5

/-! ## One step of the transfer matrix, as polynomial identities -/
private theorem q1_0 (x y z u : Rat) :
    v1_0 x y z u = x * v0_0 x y z u := by
  simp only [v0_0, v1_0]; try ring
private theorem q1_1 (x y z u : Rat) :
    v1_1 x y z u = y * v0_0 x y z u := by
  simp only [v0_0, v1_1]; try ring
private theorem q1_2 (x y z u : Rat) :
    v1_2 x y z u = z * v0_0 x y z u := by
  simp only [v0_0, v1_2]; try ring
private theorem q1_3 (x y z u : Rat) :
    v1_3 x y z u = u * v0_0 x y z u := by
  simp only [v0_0, v1_3]; try ring
private theorem q1_4 (x y z u : Rat) :
    v1_4 x y z u = u * v0_0 x y z u := by
  simp only [v0_0, v1_4]; try ring
private theorem q2_0 (x y z u : Rat) :
    v2_0 x y z u = x * v1_0 x y z u := by
  simp only [v1_0, v2_0]; try ring
private theorem q2_1 (x y z u : Rat) :
    v2_1 x y z u = y * v1_0 x y z u + y * v1_3 x y z u + z * v1_3 x y z u + u * v1_3 x y z u := by
  simp only [v1_0, v1_3, v2_1]; try ring
private theorem q2_2 (x y z u : Rat) :
    v2_2 x y z u = z * v1_0 x y z u := by
  simp only [v1_0, v2_2]; try ring
private theorem q2_3 (x y z u : Rat) :
    v2_3 x y z u = u * v1_0 x y z u := by
  simp only [v1_0, v2_3]; try ring
private theorem q2_4 (x y z u : Rat) :
    v2_4 x y z u = u * v1_0 x y z u + x * v1_3 x y z u + u * v1_3 x y z u := by
  simp only [v1_0, v1_3, v2_4]; try ring
private theorem q2_5 (x y z u : Rat) :
    v2_5 x y z u = x * v1_1 x y z u + u * v1_1 x y z u + u * v1_2 x y z u + u * v1_4 x y z u := by
  simp only [v1_1, v1_2, v1_4, v2_5]; try ring
private theorem q2_6 (x y z u : Rat) :
    v2_6 x y z u = y * v1_1 x y z u + z * v1_1 x y z u + u * v1_1 x y z u + y * v1_2 x y z u + y * v1_4 x y z u := by
  simp only [v1_1, v1_2, v1_4, v2_6]; try ring
private theorem q2_7 (x y z u : Rat) :
    v2_7 x y z u = x * v1_2 x y z u := by
  simp only [v1_2, v2_7]; try ring
private theorem q2_8 (x y z u : Rat) :
    v2_8 x y z u = z * v1_2 x y z u := by
  simp only [v1_2, v2_8]; try ring
private theorem q2_9 (x y z u : Rat) :
    v2_9 x y z u = u * v1_2 x y z u := by
  simp only [v1_2, v2_9]; try ring
private theorem q2_10 (x y z u : Rat) :
    v2_10 x y z u = x * v1_4 x y z u := by
  simp only [v1_4, v2_10]; try ring
private theorem q2_11 (x y z u : Rat) :
    v2_11 x y z u = z * v1_4 x y z u := by
  simp only [v1_4, v2_11]; try ring
private theorem q2_12 (x y z u : Rat) :
    v2_12 x y z u = u * v1_4 x y z u := by
  simp only [v1_4, v2_12]; try ring
private theorem q3_0 (x y z u : Rat) :
    v3_0 x y z u = x * v2_0 x y z u := by
  simp only [v2_0, v3_0]; try ring
private theorem q3_1 (x y z u : Rat) :
    v3_1 x y z u = y * v2_0 x y z u + y * v2_3 x y z u + z * v2_3 x y z u + u * v2_3 x y z u := by
  simp only [v2_0, v2_3, v3_1]; try ring
private theorem q3_2 (x y z u : Rat) :
    v3_2 x y z u = z * v2_0 x y z u := by
  simp only [v2_0, v3_2]; try ring
private theorem q3_3 (x y z u : Rat) :
    v3_3 x y z u = u * v2_0 x y z u := by
  simp only [v2_0, v3_3]; try ring
private theorem q3_4 (x y z u : Rat) :
    v3_4 x y z u = u * v2_0 x y z u + x * v2_3 x y z u + u * v2_3 x y z u := by
  simp only [v2_0, v2_3, v3_4]; try ring
private theorem q3_5 (x y z u : Rat) :
    v3_5 x y z u = x * v2_1 x y z u + u * v2_1 x y z u + u * v2_2 x y z u + u * v2_4 x y z u := by
  simp only [v2_1, v2_2, v2_4, v3_5]; try ring
private theorem q3_6 (x y z u : Rat) :
    v3_6 x y z u = y * v2_1 x y z u + z * v2_1 x y z u + u * v2_1 x y z u + y * v2_2 x y z u + y * v2_4 x y z u := by
  simp only [v2_1, v2_2, v2_4, v3_6]; try ring
private theorem q3_7 (x y z u : Rat) :
    v3_7 x y z u = x * v2_2 x y z u := by
  simp only [v2_2, v3_7]; try ring
private theorem q3_8 (x y z u : Rat) :
    v3_8 x y z u = z * v2_2 x y z u := by
  simp only [v2_2, v3_8]; try ring
private theorem q3_9 (x y z u : Rat) :
    v3_9 x y z u = u * v2_2 x y z u := by
  simp only [v2_2, v3_9]; try ring
private theorem q3_10 (x y z u : Rat) :
    v3_10 x y z u = x * v2_4 x y z u := by
  simp only [v2_4, v3_10]; try ring
private theorem q3_11 (x y z u : Rat) :
    v3_11 x y z u = z * v2_4 x y z u := by
  simp only [v2_4, v3_11]; try ring
private theorem q3_12 (x y z u : Rat) :
    v3_12 x y z u = u * v2_4 x y z u := by
  simp only [v2_4, v3_12]; try ring
private theorem q3_13 (x y z u : Rat) :
    v3_13 x y z u = x * v2_5 x y z u := by
  simp only [v2_5, v3_13]; try ring
private theorem q3_14 (x y z u : Rat) :
    v3_14 x y z u = y * v2_5 x y z u + y * v2_6 x y z u + z * v2_6 x y z u + u * v2_6 x y z u + y * v2_8 x y z u + y * v2_11 x y z u := by
  simp only [v2_11, v2_5, v2_6, v2_8, v3_14]; try ring
private theorem q3_15 (x y z u : Rat) :
    v3_15 x y z u = z * v2_5 x y z u := by
  simp only [v2_5, v3_15]; try ring
private theorem q3_16 (x y z u : Rat) :
    v3_16 x y z u = u * v2_5 x y z u := by
  simp only [v2_5, v3_16]; try ring
private theorem q3_17 (x y z u : Rat) :
    v3_17 x y z u = u * v2_5 x y z u + x * v2_6 x y z u + u * v2_6 x y z u + u * v2_8 x y z u + u * v2_11 x y z u := by
  simp only [v2_11, v2_5, v2_6, v2_8, v3_17]; try ring
private theorem q3_18 (x y z u : Rat) :
    v3_18 x y z u = x * v2_7 x y z u := by
  simp only [v2_7, v3_18]; try ring
private theorem q3_19 (x y z u : Rat) :
    v3_19 x y z u = y * v2_7 x y z u + y * v2_9 x y z u + z * v2_9 x y z u + u * v2_9 x y z u := by
  simp only [v2_7, v2_9, v3_19]; try ring
private theorem q3_20 (x y z u : Rat) :
    v3_20 x y z u = z * v2_7 x y z u := by
  simp only [v2_7, v3_20]; try ring
private theorem q3_21 (x y z u : Rat) :
    v3_21 x y z u = u * v2_7 x y z u := by
  simp only [v2_7, v3_21]; try ring
private theorem q3_22 (x y z u : Rat) :
    v3_22 x y z u = u * v2_7 x y z u + x * v2_9 x y z u + u * v2_9 x y z u := by
  simp only [v2_7, v2_9, v3_22]; try ring
private theorem q3_23 (x y z u : Rat) :
    v3_23 x y z u = x * v2_8 x y z u := by
  simp only [v2_8, v3_23]; try ring
private theorem q3_24 (x y z u : Rat) :
    v3_24 x y z u = z * v2_8 x y z u := by
  simp only [v2_8, v3_24]; try ring
private theorem q3_25 (x y z u : Rat) :
    v3_25 x y z u = u * v2_8 x y z u := by
  simp only [v2_8, v3_25]; try ring
private theorem q3_26 (x y z u : Rat) :
    v3_26 x y z u = x * v2_10 x y z u := by
  simp only [v2_10, v3_26]; try ring
private theorem q3_27 (x y z u : Rat) :
    v3_27 x y z u = y * v2_10 x y z u + y * v2_12 x y z u + z * v2_12 x y z u + u * v2_12 x y z u := by
  simp only [v2_10, v2_12, v3_27]; try ring
private theorem q3_28 (x y z u : Rat) :
    v3_28 x y z u = z * v2_10 x y z u := by
  simp only [v2_10, v3_28]; try ring
private theorem q3_29 (x y z u : Rat) :
    v3_29 x y z u = u * v2_10 x y z u := by
  simp only [v2_10, v3_29]; try ring
private theorem q3_30 (x y z u : Rat) :
    v3_30 x y z u = u * v2_10 x y z u + x * v2_12 x y z u + u * v2_12 x y z u := by
  simp only [v2_10, v2_12, v3_30]; try ring
private theorem q3_31 (x y z u : Rat) :
    v3_31 x y z u = x * v2_11 x y z u := by
  simp only [v2_11, v3_31]; try ring
private theorem q3_32 (x y z u : Rat) :
    v3_32 x y z u = z * v2_11 x y z u := by
  simp only [v2_11, v3_32]; try ring
private theorem q3_33 (x y z u : Rat) :
    v3_33 x y z u = u * v2_11 x y z u := by
  simp only [v2_11, v3_33]; try ring
private theorem q4_0 (x y z u : Rat) :
    v4_0 x y z u = x * v3_0 x y z u + z * v3_0 x y z u + u * v3_0 x y z u + x * v3_3 x y z u + u * v3_3 x y z u + x * v3_4 x y z u + x * v3_10 x y z u + x * v3_18 x y z u := by
  simp only [v3_0, v3_10, v3_18, v3_3, v3_4, v4_0]; try ring
private theorem q4_1 (x y z u : Rat) :
    v4_1 x y z u = y * v3_0 x y z u + u * v3_0 x y z u + y * v3_3 x y z u + z * v3_3 x y z u + u * v3_3 x y z u + u * v3_4 x y z u + u * v3_10 x y z u + u * v3_18 x y z u := by
  simp only [v3_0, v3_10, v3_18, v3_3, v3_4, v4_1]; try ring
private theorem q4_2 (x y z u : Rat) :
    v4_2 x y z u = x * v3_1 x y z u + u * v3_1 x y z u + x * v3_2 x y z u + z * v3_2 x y z u + u * v3_2 x y z u + u * v3_4 x y z u + x * v3_11 x y z u + x * v3_20 x y z u := by
  simp only [v3_1, v3_11, v3_2, v3_20, v3_4, v4_2]; try ring
private theorem q4_3 (x y z u : Rat) :
    v4_3 x y z u = y * v3_1 x y z u + z * v3_1 x y z u + u * v3_1 x y z u + y * v3_2 x y z u + u * v3_2 x y z u + y * v3_4 x y z u + u * v3_11 x y z u + u * v3_20 x y z u := by
  simp only [v3_1, v3_11, v3_2, v3_20, v3_4, v4_3]; try ring
private theorem q4_4 (x y z u : Rat) :
    v4_4 x y z u = z * v3_4 x y z u := by
  simp only [v3_4, v4_4]; try ring
private theorem q4_5 (x y z u : Rat) :
    v4_5 x y z u = x * v3_5 x y z u + x * v3_7 x y z u + z * v3_7 x y z u + u * v3_7 x y z u + x * v3_9 x y z u + u * v3_9 x y z u + x * v3_23 x y z u := by
  simp only [v3_23, v3_5, v3_7, v3_9, v4_5]; try ring
private theorem q4_6 (x y z u : Rat) :
    v4_6 x y z u = y * v3_5 x y z u + y * v3_6 x y z u + z * v3_6 x y z u + u * v3_6 x y z u + y * v3_8 x y z u + u * v3_8 x y z u + y * v3_11 x y z u + u * v3_24 x y z u := by
  simp only [v3_11, v3_24, v3_5, v3_6, v3_8, v4_6, v4_6_p0, v4_6_p1]; try ring
private theorem q4_7 (x y z u : Rat) :
    v4_7 x y z u = z * v3_5 x y z u := by
  simp only [v3_5, v4_7]; try ring
private theorem q4_8 (x y z u : Rat) :
    v4_8 x y z u = u * v3_5 x y z u + y * v3_7 x y z u + u * v3_7 x y z u + y * v3_9 x y z u + z * v3_9 x y z u + u * v3_9 x y z u + u * v3_23 x y z u := by
  simp only [v3_23, v3_5, v3_7, v3_9, v4_8]; try ring
private theorem q4_9 (x y z u : Rat) :
    v4_9 x y z u = u * v3_5 x y z u + x * v3_6 x y z u + u * v3_6 x y z u + x * v3_8 x y z u + z * v3_8 x y z u + u * v3_8 x y z u + u * v3_11 x y z u + x * v3_24 x y z u := by
  simp only [v3_11, v3_24, v3_5, v3_6, v3_8, v4_9, v4_9_p0, v4_9_p1]; try ring
private theorem q4_10 (x y z u : Rat) :
    v4_10 x y z u = y * v3_10 x y z u + y * v3_12 x y z u + z * v3_12 x y z u + u * v3_12 x y z u := by
  simp only [v3_10, v3_12, v4_10]; try ring
private theorem q4_11 (x y z u : Rat) :
    v4_11 x y z u = z * v3_10 x y z u := by
  simp only [v3_10, v4_11]; try ring
private theorem q4_12 (x y z u : Rat) :
    v4_12 x y z u = u * v3_10 x y z u + x * v3_12 x y z u + u * v3_12 x y z u := by
  simp only [v3_10, v3_12, v4_12]; try ring
private theorem q4_13 (x y z u : Rat) :
    v4_13 x y z u = z * v3_11 x y z u := by
  simp only [v3_11, v4_13]; try ring
private theorem q4_14 (x y z u : Rat) :
    v4_14 x y z u = x * v3_13 x y z u + x * v3_26 x y z u + z * v3_26 x y z u + u * v3_26 x y z u + x * v3_29 x y z u + u * v3_29 x y z u + x * v3_30 x y z u := by
  simp only [v3_13, v3_26, v3_29, v3_30, v4_14]; try ring
private theorem q4_15 (x y z u : Rat) :
    v4_15 x y z u = y * v3_13 x y z u + y * v3_16 x y z u + z * v3_16 x y z u + u * v3_16 x y z u := by
  simp only [v3_13, v3_16, v4_15]; try ring
private theorem q4_16 (x y z u : Rat) :
    v4_16 x y z u = z * v3_13 x y z u := by
  simp only [v3_13, v4_16]; try ring
private theorem q4_17 (x y z u : Rat) :
    v4_17 x y z u = u * v3_13 x y z u + y * v3_26 x y z u + u * v3_26 x y z u + y * v3_29 x y z u + z * v3_29 x y z u + u * v3_29 x y z u + u * v3_30 x y z u := by
  simp only [v3_13, v3_26, v3_29, v3_30, v4_17]; try ring
private theorem q4_18 (x y z u : Rat) :
    v4_18 x y z u = u * v3_13 x y z u + x * v3_16 x y z u + u * v3_16 x y z u := by
  simp only [v3_13, v3_16, v4_18]; try ring
private theorem q4_19 (x y z u : Rat) :
    v4_19 x y z u = x * v3_14 x y z u + u * v3_14 x y z u + u * v3_15 x y z u + u * v3_17 x y z u + u * v3_24 x y z u + x * v3_32 x y z u + z * v3_32 x y z u + u * v3_32 x y z u := by
  simp only [v3_14, v3_15, v3_17, v3_24, v3_32, v4_19, v4_19_p0, v4_19_p1]; try ring
private theorem q4_20 (x y z u : Rat) :
    v4_20 x y z u = y * v3_14 x y z u + z * v3_14 x y z u + u * v3_14 x y z u + y * v3_15 x y z u + y * v3_17 x y z u + y * v3_24 x y z u + y * v3_32 x y z u + u * v3_32 x y z u := by
  simp only [v3_14, v3_15, v3_17, v3_24, v3_32, v4_20]; try ring
private theorem q4_21 (x y z u : Rat) :
    v4_21 x y z u = x * v3_15 x y z u + x * v3_27 x y z u + u * v3_27 x y z u + x * v3_28 x y z u + z * v3_28 x y z u + u * v3_28 x y z u + u * v3_30 x y z u := by
  simp only [v3_15, v3_27, v3_28, v3_30, v4_21]; try ring
private theorem q4_22 (x y z u : Rat) :
    v4_22 x y z u = z * v3_15 x y z u := by
  simp only [v3_15, v4_22]; try ring
private theorem q4_23 (x y z u : Rat) :
    v4_23 x y z u = u * v3_15 x y z u + y * v3_27 x y z u + z * v3_27 x y z u + u * v3_27 x y z u + y * v3_28 x y z u + u * v3_28 x y z u + y * v3_30 x y z u := by
  simp only [v3_15, v3_27, v3_28, v3_30, v4_23]; try ring
private theorem q4_24 (x y z u : Rat) :
    v4_24 x y z u = x * v3_17 x y z u + x * v3_31 x y z u + z * v3_31 x y z u + u * v3_31 x y z u + x * v3_33 x y z u + u * v3_33 x y z u := by
  simp only [v3_17, v3_31, v3_33, v4_24]; try ring
private theorem q4_25 (x y z u : Rat) :
    v4_25 x y z u = z * v3_17 x y z u := by
  simp only [v3_17, v4_25]; try ring
private theorem q4_26 (x y z u : Rat) :
    v4_26 x y z u = u * v3_17 x y z u + y * v3_31 x y z u + u * v3_31 x y z u + y * v3_33 x y z u + z * v3_33 x y z u + u * v3_33 x y z u := by
  simp only [v3_17, v3_31, v3_33, v4_26]; try ring
private theorem q4_27 (x y z u : Rat) :
    v4_27 x y z u = y * v3_18 x y z u + y * v3_21 x y z u + z * v3_21 x y z u + u * v3_21 x y z u := by
  simp only [v3_18, v3_21, v4_27]; try ring
private theorem q4_28 (x y z u : Rat) :
    v4_28 x y z u = z * v3_18 x y z u := by
  simp only [v3_18, v4_28]; try ring
private theorem q4_29 (x y z u : Rat) :
    v4_29 x y z u = u * v3_18 x y z u + x * v3_21 x y z u + u * v3_21 x y z u := by
  simp only [v3_18, v3_21, v4_29]; try ring
private theorem q4_30 (x y z u : Rat) :
    v4_30 x y z u = x * v3_19 x y z u + u * v3_19 x y z u + u * v3_20 x y z u + u * v3_22 x y z u := by
  simp only [v3_19, v3_20, v3_22, v4_30]; try ring
private theorem q4_31 (x y z u : Rat) :
    v4_31 x y z u = y * v3_19 x y z u + z * v3_19 x y z u + u * v3_19 x y z u + y * v3_20 x y z u + y * v3_22 x y z u := by
  simp only [v3_19, v3_20, v3_22, v4_31]; try ring
private theorem q4_32 (x y z u : Rat) :
    v4_32 x y z u = z * v3_20 x y z u := by
  simp only [v3_20, v4_32]; try ring
private theorem q4_33 (x y z u : Rat) :
    v4_33 x y z u = x * v3_22 x y z u := by
  simp only [v3_22, v4_33]; try ring
private theorem q4_34 (x y z u : Rat) :
    v4_34 x y z u = z * v3_22 x y z u := by
  simp only [v3_22, v4_34]; try ring
private theorem q4_35 (x y z u : Rat) :
    v4_35 x y z u = u * v3_22 x y z u := by
  simp only [v3_22, v4_35]; try ring
private theorem q4_36 (x y z u : Rat) :
    v4_36 x y z u = y * v3_23 x y z u + y * v3_25 x y z u + z * v3_25 x y z u + u * v3_25 x y z u := by
  simp only [v3_23, v3_25, v4_36]; try ring
private theorem q4_37 (x y z u : Rat) :
    v4_37 x y z u = z * v3_23 x y z u := by
  simp only [v3_23, v4_37]; try ring
private theorem q4_38 (x y z u : Rat) :
    v4_38 x y z u = u * v3_23 x y z u + x * v3_25 x y z u + u * v3_25 x y z u := by
  simp only [v3_23, v3_25, v4_38]; try ring
private theorem q4_39 (x y z u : Rat) :
    v4_39 x y z u = z * v3_24 x y z u := by
  simp only [v3_24, v4_39]; try ring
private theorem q4_40 (x y z u : Rat) :
    v4_40 x y z u = z * v3_30 x y z u := by
  simp only [v3_30, v4_40]; try ring
private theorem q5_0 (x y z u : Rat) :
    v5_0 x y z u = x * v4_0 x y z u + z * v4_0 x y z u + u * v4_0 x y z u + x * v4_1 x y z u + u * v4_1 x y z u + x * v4_2 x y z u + x * v4_12 x y z u + x * v4_29 x y z u := by
  simp only [v4_0, v4_1, v4_12, v4_2, v4_29, v5_0]; try ring
private theorem q5_1 (x y z u : Rat) :
    v5_1 x y z u = y * v4_0 x y z u + u * v4_0 x y z u + y * v4_1 x y z u + z * v4_1 x y z u + u * v4_1 x y z u + u * v4_2 x y z u + u * v4_12 x y z u + u * v4_29 x y z u := by
  simp only [v4_0, v4_1, v4_12, v4_2, v4_29, v5_1, v5_1_p0, v5_1_p1]; try ring
private theorem q5_2 (x y z u : Rat) :
    v5_2 x y z u = y * v4_2 x y z u + y * v4_3 x y z u + z * v4_3 x y z u + u * v4_3 x y z u + y * v4_4 x y z u + u * v4_4 x y z u := by
  simp only [v4_2, v4_3, v4_4, v5_2, v5_2_p0, v5_2_p1]; try ring
private theorem q5_3 (x y z u : Rat) :
    v5_3 x y z u = z * v4_2 x y z u := by
  simp only [v4_2, v5_3]; try ring
private theorem q5_4 (x y z u : Rat) :
    v5_4 x y z u = u * v4_2 x y z u + x * v4_3 x y z u + u * v4_3 x y z u + x * v4_4 x y z u + z * v4_4 x y z u + u * v4_4 x y z u := by
  simp only [v4_2, v4_3, v4_4, v5_4, v5_4_p0, v5_4_p1]; try ring
private theorem q5_5 (x y z u : Rat) :
    v5_5 x y z u = x * v4_5 x y z u + z * v4_5 x y z u + u * v4_5 x y z u + x * v4_8 x y z u + u * v4_8 x y z u + x * v4_9 x y z u + x * v4_38 x y z u := by
  simp only [v4_38, v4_5, v4_8, v4_9, v4_9_p0, v4_9_p1, v5_5, v5_5_p0, v5_5_p1]; try ring
private theorem q5_6 (x y z u : Rat) :
    v5_6 x y z u = y * v4_5 x y z u + u * v4_5 x y z u + y * v4_8 x y z u + z * v4_8 x y z u + u * v4_8 x y z u + u * v4_9 x y z u + u * v4_38 x y z u := by
  simp only [v4_38, v4_5, v4_8, v4_9, v4_9_p0, v4_9_p1, v5_6, v5_6_p0, v5_6_p1]; try ring
private theorem q5_7 (x y z u : Rat) :
    v5_7 x y z u = x * v4_6 x y z u + u * v4_6 x y z u + x * v4_7 x y z u + z * v4_7 x y z u + u * v4_7 x y z u + u * v4_9 x y z u + u * v4_13 x y z u := by
  simp only [v4_13, v4_6, v4_6_p0, v4_6_p1, v4_7, v4_9, v4_9_p0, v4_9_p1, v5_7, v5_7_p0, v5_7_p1, v5_7_p2]; try ring
private theorem q5_8 (x y z u : Rat) :
    v5_8 x y z u = y * v4_6 x y z u + z * v4_6 x y z u + u * v4_6 x y z u + y * v4_7 x y z u + u * v4_7 x y z u + y * v4_9 x y z u + y * v4_13 x y z u := by
  simp only [v4_13, v4_6, v4_6_p0, v4_6_p1, v4_7, v4_9, v4_9_p0, v4_9_p1, v5_8, v5_8_p0, v5_8_p1, v5_8_p2]; try ring
private theorem q5_9 (x y z u : Rat) :
    v5_9 x y z u = z * v4_9 x y z u := by
  simp only [v4_9, v4_9_p0, v4_9_p1, v5_9, v5_9_p0, v5_9_p1]; try ring
private theorem q5_10 (x y z u : Rat) :
    v5_10 x y z u = x * v4_10 x y z u + u * v4_10 x y z u + x * v4_11 x y z u + z * v4_11 x y z u + u * v4_11 x y z u + u * v4_12 x y z u + x * v4_13 x y z u := by
  simp only [v4_10, v4_11, v4_12, v4_13, v5_10]; try ring
private theorem q5_11 (x y z u : Rat) :
    v5_11 x y z u = y * v4_10 x y z u + z * v4_10 x y z u + u * v4_10 x y z u + y * v4_11 x y z u + u * v4_11 x y z u + y * v4_12 x y z u + u * v4_13 x y z u := by
  simp only [v4_10, v4_11, v4_12, v4_13, v5_11]; try ring
private theorem q5_12 (x y z u : Rat) :
    v5_12 x y z u = z * v4_12 x y z u := by
  simp only [v4_12, v5_12]; try ring
private theorem q5_13 (x y z u : Rat) :
    v5_13 x y z u = z * v4_13 x y z u := by
  simp only [v4_13, v5_13]; try ring
private theorem q5_14 (x y z u : Rat) :
    v5_14 x y z u = x * v4_14 x y z u + z * v4_14 x y z u + u * v4_14 x y z u + x * v4_17 x y z u + u * v4_17 x y z u + x * v4_18 x y z u + x * v4_21 x y z u := by
  simp only [v4_14, v4_17, v4_18, v4_21, v5_14]; try ring
private theorem q5_15 (x y z u : Rat) :
    v5_15 x y z u = y * v4_14 x y z u + u * v4_14 x y z u + y * v4_17 x y z u + z * v4_17 x y z u + u * v4_17 x y z u + u * v4_18 x y z u + u * v4_21 x y z u := by
  simp only [v4_14, v4_17, v4_18, v4_21, v5_15, v5_15_p0, v5_15_p1]; try ring
private theorem q5_16 (x y z u : Rat) :
    v5_16 x y z u = x * v4_15 x y z u + u * v4_15 x y z u + x * v4_16 x y z u + z * v4_16 x y z u + u * v4_16 x y z u + u * v4_18 x y z u + x * v4_22 x y z u := by
  simp only [v4_15, v4_16, v4_18, v4_22, v5_16, v5_16_p0, v5_16_p1]; try ring
private theorem q5_17 (x y z u : Rat) :
    v5_17 x y z u = y * v4_15 x y z u + z * v4_15 x y z u + u * v4_15 x y z u + y * v4_16 x y z u + u * v4_16 x y z u + y * v4_18 x y z u + u * v4_22 x y z u := by
  simp only [v4_15, v4_16, v4_18, v4_22, v5_17, v5_17_p0, v5_17_p1]; try ring
private theorem q5_18 (x y z u : Rat) :
    v5_18 x y z u = z * v4_18 x y z u := by
  simp only [v4_18, v5_18]; try ring
private theorem q5_19 (x y z u : Rat) :
    v5_19 x y z u = x * v4_19 x y z u + x * v4_24 x y z u + z * v4_24 x y z u + u * v4_24 x y z u + x * v4_26 x y z u + u * v4_26 x y z u := by
  simp only [v4_19, v4_19_p0, v4_19_p1, v4_24, v4_26, v5_19, v5_19_p0, v5_19_p1, v5_19_p2]; try ring
private theorem q5_20 (x y z u : Rat) :
    v5_20 x y z u = y * v4_19 x y z u + y * v4_20 x y z u + z * v4_20 x y z u + u * v4_20 x y z u + y * v4_22 x y z u + y * v4_25 x y z u + u * v4_25 x y z u + y * v4_39 x y z u := by
  simp only [v4_19, v4_19_p0, v4_19_p1, v4_20, v4_22, v4_25, v4_39, v5_20, v5_20_p0, v5_20_p1]; try ring
private theorem q5_21 (x y z u : Rat) :
    v5_21 x y z u = z * v4_19 x y z u := by
  simp only [v4_19, v4_19_p0, v4_19_p1, v5_21, v5_21_p0, v5_21_p1]; try ring
private theorem q5_22 (x y z u : Rat) :
    v5_22 x y z u = u * v4_19 x y z u + y * v4_24 x y z u + u * v4_24 x y z u + y * v4_26 x y z u + z * v4_26 x y z u + u * v4_26 x y z u := by
  simp only [v4_19, v4_19_p0, v4_19_p1, v4_24, v4_26, v5_22, v5_22_p0, v5_22_p1]; try ring
private theorem q5_23 (x y z u : Rat) :
    v5_23 x y z u = u * v4_19 x y z u + x * v4_20 x y z u + u * v4_20 x y z u + u * v4_22 x y z u + x * v4_25 x y z u + z * v4_25 x y z u + u * v4_25 x y z u + u * v4_39 x y z u := by
  simp only [v4_19, v4_19_p0, v4_19_p1, v4_20, v4_22, v4_25, v4_39, v5_23, v5_23_p0, v5_23_p1, v5_23_p2]; try ring
private theorem q5_24 (x y z u : Rat) :
    v5_24 x y z u = y * v4_21 x y z u + y * v4_23 x y z u + z * v4_23 x y z u + u * v4_23 x y z u + y * v4_40 x y z u + u * v4_40 x y z u := by
  simp only [v4_21, v4_23, v4_40, v5_24, v5_24_p0, v5_24_p1]; try ring
private theorem q5_25 (x y z u : Rat) :
    v5_25 x y z u = z * v4_21 x y z u := by
  simp only [v4_21, v5_25]; try ring
private theorem q5_26 (x y z u : Rat) :
    v5_26 x y z u = u * v4_21 x y z u + x * v4_23 x y z u + u * v4_23 x y z u + x * v4_40 x y z u + z * v4_40 x y z u + u * v4_40 x y z u := by
  simp only [v4_21, v4_23, v4_40, v5_26]; try ring
private theorem q5_27 (x y z u : Rat) :
    v5_27 x y z u = z * v4_22 x y z u := by
  simp only [v4_22, v5_27]; try ring
private theorem q5_28 (x y z u : Rat) :
    v5_28 x y z u = x * v4_27 x y z u + u * v4_27 x y z u + x * v4_28 x y z u + z * v4_28 x y z u + u * v4_28 x y z u + u * v4_29 x y z u + x * v4_32 x y z u := by
  simp only [v4_27, v4_28, v4_29, v4_32, v5_28]; try ring
private theorem q5_29 (x y z u : Rat) :
    v5_29 x y z u = y * v4_27 x y z u + z * v4_27 x y z u + u * v4_27 x y z u + y * v4_28 x y z u + u * v4_28 x y z u + y * v4_29 x y z u + u * v4_32 x y z u := by
  simp only [v4_27, v4_28, v4_29, v4_32, v5_29]; try ring
private theorem q5_30 (x y z u : Rat) :
    v5_30 x y z u = z * v4_29 x y z u := by
  simp only [v4_29, v5_30]; try ring
private theorem q5_31 (x y z u : Rat) :
    v5_31 x y z u = x * v4_30 x y z u + x * v4_33 x y z u + z * v4_33 x y z u + u * v4_33 x y z u + x * v4_35 x y z u + u * v4_35 x y z u := by
  simp only [v4_30, v4_33, v4_35, v5_31]; try ring
private theorem q5_32 (x y z u : Rat) :
    v5_32 x y z u = y * v4_30 x y z u + y * v4_31 x y z u + z * v4_31 x y z u + u * v4_31 x y z u + y * v4_32 x y z u + y * v4_34 x y z u + u * v4_34 x y z u := by
  simp only [v4_30, v4_31, v4_32, v4_34, v5_32, v5_32_p0, v5_32_p1]; try ring
private theorem q5_33 (x y z u : Rat) :
    v5_33 x y z u = z * v4_30 x y z u := by
  simp only [v4_30, v5_33]; try ring
private theorem q5_34 (x y z u : Rat) :
    v5_34 x y z u = u * v4_30 x y z u + y * v4_33 x y z u + u * v4_33 x y z u + y * v4_35 x y z u + z * v4_35 x y z u + u * v4_35 x y z u := by
  simp only [v4_30, v4_33, v4_35, v5_34]; try ring
private theorem q5_35 (x y z u : Rat) :
    v5_35 x y z u = u * v4_30 x y z u + x * v4_31 x y z u + u * v4_31 x y z u + u * v4_32 x y z u + x * v4_34 x y z u + z * v4_34 x y z u + u * v4_34 x y z u := by
  simp only [v4_30, v4_31, v4_32, v4_34, v5_35]; try ring
private theorem q5_36 (x y z u : Rat) :
    v5_36 x y z u = z * v4_32 x y z u := by
  simp only [v4_32, v5_36]; try ring
private theorem q5_37 (x y z u : Rat) :
    v5_37 x y z u = x * v4_36 x y z u + u * v4_36 x y z u + x * v4_37 x y z u + z * v4_37 x y z u + u * v4_37 x y z u + u * v4_38 x y z u + x * v4_39 x y z u := by
  simp only [v4_36, v4_37, v4_38, v4_39, v5_37]; try ring
private theorem q5_38 (x y z u : Rat) :
    v5_38 x y z u = y * v4_36 x y z u + z * v4_36 x y z u + u * v4_36 x y z u + y * v4_37 x y z u + u * v4_37 x y z u + y * v4_38 x y z u + u * v4_39 x y z u := by
  simp only [v4_36, v4_37, v4_38, v4_39, v5_38]; try ring
private theorem q5_39 (x y z u : Rat) :
    v5_39 x y z u = z * v4_38 x y z u := by
  simp only [v4_38, v5_39]; try ring
private theorem q5_40 (x y z u : Rat) :
    v5_40 x y z u = z * v4_39 x y z u := by
  simp only [v4_39, v5_40]; try ring
private theorem q6_0 (x y z u : Rat) :
    wF0 x y z u = x * v5_0 x y z u + z * v5_0 x y z u + u * v5_0 x y z u + x * v5_1 x y z u + u * v5_1 x y z u + x * v5_4 x y z u + x * v5_5 x y z u + x * v5_12 x y z u + x * v5_30 x y z u + x * v5_31 x y z u := by
  simp only [v5_0, v5_1, v5_12, v5_1_p0, v5_1_p1, v5_30, v5_31, v5_4, v5_4_p0, v5_4_p1, v5_5, v5_5_p0, v5_5_p1, wF0]; try ring
private theorem q6_1 (x y z u : Rat) :
    wF1 x y z u = y * v5_0 x y z u + u * v5_0 x y z u + y * v5_1 x y z u + z * v5_1 x y z u + u * v5_1 x y z u + u * v5_4 x y z u + u * v5_5 x y z u + u * v5_12 x y z u + u * v5_30 x y z u + u * v5_31 x y z u := by
  simp only [v5_0, v5_1, v5_12, v5_1_p0, v5_1_p1, v5_30, v5_31, v5_4, v5_4_p0, v5_4_p1, v5_5, v5_5_p0, v5_5_p1, wF1]; try ring
private theorem q6_2 (x y z u : Rat) :
    wF2 x y z u = x * v5_2 x y z u + u * v5_2 x y z u + x * v5_3 x y z u + z * v5_3 x y z u + u * v5_3 x y z u + u * v5_4 x y z u + x * v5_9 x y z u + x * v5_33 x y z u := by
  simp only [v5_2, v5_2_p0, v5_2_p1, v5_3, v5_33, v5_4, v5_4_p0, v5_4_p1, v5_9, v5_9_p0, v5_9_p1, wF2]; try ring
private theorem q6_3 (x y z u : Rat) :
    wF3 x y z u = y * v5_2 x y z u + z * v5_2 x y z u + u * v5_2 x y z u + y * v5_3 x y z u + u * v5_3 x y z u + y * v5_4 x y z u + u * v5_9 x y z u + u * v5_33 x y z u := by
  simp only [v5_2, v5_2_p0, v5_2_p1, v5_3, v5_33, v5_4, v5_4_p0, v5_4_p1, v5_9, v5_9_p0, v5_9_p1, wF3]; try ring
private theorem q6_4 (x y z u : Rat) :
    wF4 x y z u = z * v5_4 x y z u := by
  simp only [v5_4, v5_4_p0, v5_4_p1, wF4]; try ring
private theorem q6_5 (x y z u : Rat) :
    wF5 x y z u = y * v5_5 x y z u + y * v5_6 x y z u + z * v5_6 x y z u + u * v5_6 x y z u := by
  simp only [v5_5, v5_5_p0, v5_5_p1, v5_6, v5_6_p0, v5_6_p1, wF5]; try ring
private theorem q6_6 (x y z u : Rat) :
    wF6 x y z u = z * v5_5 x y z u := by
  simp only [v5_5, v5_5_p0, v5_5_p1, wF6]; try ring
private theorem q6_7 (x y z u : Rat) :
    wF7 x y z u = u * v5_5 x y z u + x * v5_6 x y z u + u * v5_6 x y z u := by
  simp only [v5_5, v5_5_p0, v5_5_p1, v5_6, v5_6_p0, v5_6_p1, wF7]; try ring
private theorem q6_8 (x y z u : Rat) :
    wF8 x y z u = x * v5_7 x y z u + x * v5_10 x y z u + z * v5_10 x y z u + u * v5_10 x y z u + x * v5_11 x y z u + u * v5_11 x y z u + u * v5_12 x y z u := by
  simp only [v5_10, v5_11, v5_12, v5_7, v5_7_p0, v5_7_p1, v5_7_p2, wF8]; try ring
private theorem q6_9 (x y z u : Rat) :
    wF9 x y z u = y * v5_7 x y z u + y * v5_8 x y z u + z * v5_8 x y z u + u * v5_8 x y z u + y * v5_9 x y z u + y * v5_13 x y z u + u * v5_13 x y z u := by
  simp only [v5_13, v5_7, v5_7_p0, v5_7_p1, v5_7_p2, v5_8, v5_8_p0, v5_8_p1, v5_8_p2, v5_9, v5_9_p0, v5_9_p1, wF9]; try ring
private theorem q6_10 (x y z u : Rat) :
    wF10 x y z u = z * v5_7 x y z u := by
  simp only [v5_7, v5_7_p0, v5_7_p1, v5_7_p2, wF10]; try ring
private theorem q6_11 (x y z u : Rat) :
    wF11 x y z u = u * v5_7 x y z u + y * v5_10 x y z u + u * v5_10 x y z u + y * v5_11 x y z u + z * v5_11 x y z u + u * v5_11 x y z u + y * v5_12 x y z u := by
  simp only [v5_10, v5_11, v5_12, v5_7, v5_7_p0, v5_7_p1, v5_7_p2, wF11]; try ring
private theorem q6_12 (x y z u : Rat) :
    wF12 x y z u = u * v5_7 x y z u + x * v5_8 x y z u + u * v5_8 x y z u + u * v5_9 x y z u + x * v5_13 x y z u + z * v5_13 x y z u + u * v5_13 x y z u := by
  simp only [v5_13, v5_7, v5_7_p0, v5_7_p1, v5_7_p2, v5_8, v5_8_p0, v5_8_p1, v5_8_p2, v5_9, v5_9_p0, v5_9_p1, wF12]; try ring
private theorem q6_13 (x y z u : Rat) :
    wF13 x y z u = z * v5_9 x y z u := by
  simp only [v5_9, v5_9_p0, v5_9_p1, wF13]; try ring
private theorem q6_14 (x y z u : Rat) :
    wF14 x y z u = z * v5_12 x y z u := by
  simp only [v5_12, wF14]; try ring
private theorem q6_15 (x y z u : Rat) :
    wF15 x y z u = x * v5_14 x y z u + z * v5_14 x y z u + u * v5_14 x y z u + x * v5_15 x y z u + u * v5_15 x y z u + x * v5_18 x y z u + x * v5_19 x y z u + x * v5_26 x y z u := by
  simp only [v5_14, v5_15, v5_15_p0, v5_15_p1, v5_18, v5_19, v5_19_p0, v5_19_p1, v5_19_p2, v5_26, wF15]; try ring
private theorem q6_16 (x y z u : Rat) :
    wF16 x y z u = y * v5_14 x y z u + u * v5_14 x y z u + y * v5_15 x y z u + z * v5_15 x y z u + u * v5_15 x y z u + u * v5_18 x y z u + u * v5_19 x y z u + u * v5_26 x y z u := by
  simp only [v5_14, v5_15, v5_15_p0, v5_15_p1, v5_18, v5_19, v5_19_p0, v5_19_p1, v5_19_p2, v5_26, wF16]; try ring
private theorem q6_17 (x y z u : Rat) :
    wF17 x y z u = x * v5_16 x y z u + z * v5_16 x y z u + u * v5_16 x y z u + x * v5_17 x y z u + u * v5_17 x y z u + u * v5_18 x y z u + x * v5_23 x y z u := by
  simp only [v5_16, v5_16_p0, v5_16_p1, v5_17, v5_17_p0, v5_17_p1, v5_18, v5_23, v5_23_p0, v5_23_p1, v5_23_p2, wF17]; try ring
private theorem q6_18 (x y z u : Rat) :
    wF18 x y z u = y * v5_16 x y z u + u * v5_16 x y z u + y * v5_17 x y z u + z * v5_17 x y z u + u * v5_17 x y z u + y * v5_18 x y z u + u * v5_23 x y z u := by
  simp only [v5_16, v5_16_p0, v5_16_p1, v5_17, v5_17_p0, v5_17_p1, v5_18, v5_23, v5_23_p0, v5_23_p1, v5_23_p2, wF18]; try ring
private theorem q6_19 (x y z u : Rat) :
    wF19 x y z u = z * v5_18 x y z u := by
  simp only [v5_18, wF19]; try ring
private theorem q6_20 (x y z u : Rat) :
    wF20 x y z u = y * v5_19 x y z u + y * v5_22 x y z u + z * v5_22 x y z u + u * v5_22 x y z u := by
  simp only [v5_19, v5_19_p0, v5_19_p1, v5_19_p2, v5_22, v5_22_p0, v5_22_p1, wF20]; try ring
private theorem q6_21 (x y z u : Rat) :
    wF21 x y z u = z * v5_19 x y z u := by
  simp only [v5_19, v5_19_p0, v5_19_p1, v5_19_p2, wF21]; try ring
private theorem q6_22 (x y z u : Rat) :
    wF22 x y z u = u * v5_19 x y z u + x * v5_22 x y z u + u * v5_22 x y z u := by
  simp only [v5_19, v5_19_p0, v5_19_p1, v5_19_p2, v5_22, v5_22_p0, v5_22_p1, wF22]; try ring
private theorem q6_23 (x y z u : Rat) :
    wF23 x y z u = x * v5_20 x y z u + u * v5_20 x y z u + u * v5_21 x y z u + u * v5_23 x y z u + x * v5_27 x y z u + z * v5_27 x y z u + u * v5_27 x y z u + u * v5_40 x y z u := by
  simp only [v5_20, v5_20_p0, v5_20_p1, v5_21, v5_21_p0, v5_21_p1, v5_23, v5_23_p0, v5_23_p1, v5_23_p2, v5_27, v5_40, wF23]; try ring
private theorem q6_24 (x y z u : Rat) :
    wF24 x y z u = y * v5_20 x y z u + z * v5_20 x y z u + u * v5_20 x y z u + y * v5_21 x y z u + y * v5_23 x y z u + y * v5_27 x y z u + u * v5_27 x y z u + y * v5_40 x y z u := by
  simp only [v5_20, v5_20_p0, v5_20_p1, v5_21, v5_21_p0, v5_21_p1, v5_23, v5_23_p0, v5_23_p1, v5_23_p2, v5_27, v5_40, wF24]; try ring
private theorem q6_25 (x y z u : Rat) :
    wF25 x y z u = x * v5_21 x y z u + x * v5_24 x y z u + u * v5_24 x y z u + x * v5_25 x y z u + z * v5_25 x y z u + u * v5_25 x y z u + u * v5_26 x y z u := by
  simp only [v5_21, v5_21_p0, v5_21_p1, v5_24, v5_24_p0, v5_24_p1, v5_25, v5_26, wF25]; try ring
private theorem q6_26 (x y z u : Rat) :
    wF26 x y z u = z * v5_21 x y z u := by
  simp only [v5_21, v5_21_p0, v5_21_p1, wF26]; try ring
private theorem q6_27 (x y z u : Rat) :
    wF27 x y z u = u * v5_21 x y z u + y * v5_24 x y z u + z * v5_24 x y z u + u * v5_24 x y z u + y * v5_25 x y z u + u * v5_25 x y z u + y * v5_26 x y z u := by
  simp only [v5_21, v5_21_p0, v5_21_p1, v5_24, v5_24_p0, v5_24_p1, v5_25, v5_26, wF27]; try ring
private theorem q6_28 (x y z u : Rat) :
    wF28 x y z u = z * v5_23 x y z u := by
  simp only [v5_23, v5_23_p0, v5_23_p1, v5_23_p2, wF28]; try ring
private theorem q6_29 (x y z u : Rat) :
    wF29 x y z u = z * v5_26 x y z u := by
  simp only [v5_26, wF29]; try ring
private theorem q6_30 (x y z u : Rat) :
    wF30 x y z u = x * v5_28 x y z u + z * v5_28 x y z u + u * v5_28 x y z u + x * v5_29 x y z u + u * v5_29 x y z u + u * v5_30 x y z u + x * v5_35 x y z u + x * v5_37 x y z u := by
  simp only [v5_28, v5_29, v5_30, v5_35, v5_37, wF30]; try ring
private theorem q6_31 (x y z u : Rat) :
    wF31 x y z u = y * v5_28 x y z u + u * v5_28 x y z u + y * v5_29 x y z u + z * v5_29 x y z u + u * v5_29 x y z u + y * v5_30 x y z u + u * v5_35 x y z u + u * v5_37 x y z u := by
  simp only [v5_28, v5_29, v5_30, v5_35, v5_37, wF31]; try ring
private theorem q6_32 (x y z u : Rat) :
    wF32 x y z u = z * v5_30 x y z u := by
  simp only [v5_30, wF32]; try ring
private theorem q6_33 (x y z u : Rat) :
    wF33 x y z u = y * v5_31 x y z u + y * v5_34 x y z u + z * v5_34 x y z u + u * v5_34 x y z u := by
  simp only [v5_31, v5_34, wF33]; try ring
private theorem q6_34 (x y z u : Rat) :
    wF34 x y z u = z * v5_31 x y z u := by
  simp only [v5_31, wF34]; try ring
private theorem q6_35 (x y z u : Rat) :
    wF35 x y z u = u * v5_31 x y z u + x * v5_34 x y z u + u * v5_34 x y z u := by
  simp only [v5_31, v5_34, wF35]; try ring
private theorem q6_36 (x y z u : Rat) :
    wF36 x y z u = x * v5_32 x y z u + u * v5_32 x y z u + u * v5_33 x y z u + u * v5_35 x y z u + x * v5_36 x y z u + z * v5_36 x y z u + u * v5_36 x y z u + x * v5_40 x y z u := by
  simp only [v5_32, v5_32_p0, v5_32_p1, v5_33, v5_35, v5_36, v5_40, wF36]; try ring
private theorem q6_37 (x y z u : Rat) :
    wF37 x y z u = y * v5_32 x y z u + z * v5_32 x y z u + u * v5_32 x y z u + y * v5_33 x y z u + y * v5_35 x y z u + y * v5_36 x y z u + u * v5_36 x y z u + u * v5_40 x y z u := by
  simp only [v5_32, v5_32_p0, v5_32_p1, v5_33, v5_35, v5_36, v5_40, wF37]; try ring
private theorem q6_38 (x y z u : Rat) :
    wF38 x y z u = z * v5_33 x y z u := by
  simp only [v5_33, wF38]; try ring
private theorem q6_39 (x y z u : Rat) :
    wF39 x y z u = z * v5_35 x y z u := by
  simp only [v5_35, wF39]; try ring
private theorem q6_40 (x y z u : Rat) :
    wF40 x y z u = y * v5_37 x y z u + y * v5_38 x y z u + z * v5_38 x y z u + u * v5_38 x y z u + y * v5_39 x y z u := by
  simp only [v5_37, v5_38, v5_39, wF40]; try ring
private theorem q6_41 (x y z u : Rat) :
    wF41 x y z u = z * v5_37 x y z u := by
  simp only [v5_37, wF41]; try ring
private theorem q6_42 (x y z u : Rat) :
    wF42 x y z u = u * v5_37 x y z u + x * v5_38 x y z u + u * v5_38 x y z u + u * v5_39 x y z u := by
  simp only [v5_37, v5_38, v5_39, wF42]; try ring
private theorem q6_43 (x y z u : Rat) :
    wF43 x y z u = x * v5_39 x y z u := by
  simp only [v5_39, wF43]; try ring
private theorem q6_44 (x y z u : Rat) :
    wF44 x y z u = z * v5_39 x y z u := by
  simp only [v5_39, wF44]; try ring
private theorem q6_45 (x y z u : Rat) :
    wF45 x y z u = u * v5_39 x y z u := by
  simp only [v5_39, wF45]; try ring
private theorem q6_46 (x y z u : Rat) :
    wF46 x y z u = z * v5_40 x y z u := by
  simp only [v5_40, wF46]; try ring

/-! ## The state transitions -/
private theorem tr0_0_0 : step 0 WZ.abc ![0, 1, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr0_0_1 : step 0 WZ.a_b_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 4] := by decide
private theorem tr0_0_2 : step 0 WZ.a_bc ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 0] := by decide
private theorem tr0_0_3 : step 0 WZ.ab_c ![0, 1, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr0_0_4 : step 0 WZ.ac_b ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 1] := by decide
private theorem tr1_0_0 : step 1 WZ.abc ![0, 0, 2, 3, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr1_0_1 : step 1 WZ.a_b_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr1_0_2 : step 1 WZ.a_bc ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr1_0_3 : step 1 WZ.ab_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr1_0_4 : step 1 WZ.ac_b ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 3] := by decide
private theorem tr1_1_0 : step 1 WZ.abc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 3] := by decide
private theorem tr1_1_1 : step 1 WZ.a_b_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr1_1_2 : step 1 WZ.a_bc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr1_1_3 : step 1 WZ.ab_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr1_1_4 : step 1 WZ.ac_b ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 3] := by decide
private theorem tr1_2_0 : step 1 WZ.abc ![0, 1, 2, 3, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr1_2_1 : step 1 WZ.a_b_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 4] := by decide
private theorem tr1_2_2 : step 1 WZ.a_bc ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 0] := by decide
private theorem tr1_2_3 : step 1 WZ.ab_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr1_2_4 : step 1 WZ.ac_b ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 3] := by decide
private theorem tr1_3_0 : step 1 WZ.abc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 3] := by decide
private theorem tr1_3_1 : step 1 WZ.a_b_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr1_3_2 : step 1 WZ.a_bc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr1_3_3 : step 1 WZ.ab_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr1_3_4 : step 1 WZ.ac_b ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 3] := by decide
private theorem tr1_4_0 : step 1 WZ.abc ![0, 1, 2, 3, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr1_4_1 : step 1 WZ.a_b_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 4] := by decide
private theorem tr1_4_2 : step 1 WZ.a_bc ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr1_4_3 : step 1 WZ.ab_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr1_4_4 : step 1 WZ.ac_b ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 3] := by decide
private theorem tr2_0_0 : step 2 WZ.abc ![0, 0, 2, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr2_0_1 : step 2 WZ.a_b_c ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr2_0_2 : step 2 WZ.a_bc ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr2_0_3 : step 2 WZ.ab_c ![0, 0, 2, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr2_0_4 : step 2 WZ.ac_b ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 2] := by decide
private theorem tr2_1_0 : step 2 WZ.abc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 2] := by decide
private theorem tr2_1_1 : step 2 WZ.a_b_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr2_1_2 : step 2 WZ.a_bc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr2_1_3 : step 2 WZ.ab_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr2_1_4 : step 2 WZ.ac_b ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 2] := by decide
private theorem tr2_2_0 : step 2 WZ.abc ![0, 0, 2, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr2_2_1 : step 2 WZ.a_b_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr2_2_2 : step 2 WZ.a_bc ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr2_2_3 : step 2 WZ.ab_c ![0, 0, 2, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr2_2_4 : step 2 WZ.ac_b ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 2] := by decide
private theorem tr2_3_0 : step 2 WZ.abc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 2] := by decide
private theorem tr2_3_1 : step 2 WZ.a_b_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr2_3_2 : step 2 WZ.a_bc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr2_3_3 : step 2 WZ.ab_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr2_3_4 : step 2 WZ.ac_b ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 2] := by decide
private theorem tr2_4_0 : step 2 WZ.abc ![0, 0, 2, 3, 3] = ![0, 0, 2, 2, 2] := by decide
private theorem tr2_4_1 : step 2 WZ.a_b_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 4] := by decide
private theorem tr2_4_2 : step 2 WZ.a_bc ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 3] := by decide
private theorem tr2_4_3 : step 2 WZ.ab_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 2, 4] := by decide
private theorem tr2_4_4 : step 2 WZ.ac_b ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 2] := by decide
private theorem tr2_5_0 : step 2 WZ.abc ![0, 1, 2, 3, 3] = ![0, 1, 2, 2, 2] := by decide
private theorem tr2_5_1 : step 2 WZ.a_b_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 4] := by decide
private theorem tr2_5_2 : step 2 WZ.a_bc ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 3] := by decide
private theorem tr2_5_3 : step 2 WZ.ab_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 2, 4] := by decide
private theorem tr2_5_4 : step 2 WZ.ac_b ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 2] := by decide
private theorem tr2_6_0 : step 2 WZ.abc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 2] := by decide
private theorem tr2_6_1 : step 2 WZ.a_b_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr2_6_2 : step 2 WZ.a_bc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr2_6_3 : step 2 WZ.ab_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr2_6_4 : step 2 WZ.ac_b ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 2] := by decide
private theorem tr2_7_0 : step 2 WZ.abc ![0, 1, 2, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr2_7_1 : step 2 WZ.a_b_c ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr2_7_2 : step 2 WZ.a_bc ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr2_7_3 : step 2 WZ.ab_c ![0, 1, 2, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr2_7_4 : step 2 WZ.ac_b ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 2] := by decide
private theorem tr2_8_0 : step 2 WZ.abc ![0, 1, 2, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr2_8_1 : step 2 WZ.a_b_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 4] := by decide
private theorem tr2_8_2 : step 2 WZ.a_bc ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 0] := by decide
private theorem tr2_8_3 : step 2 WZ.ab_c ![0, 1, 2, 3, 0] = ![0, 1, 0, 3, 4] := by decide
private theorem tr2_8_4 : step 2 WZ.ac_b ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 2] := by decide
private theorem tr2_9_0 : step 2 WZ.abc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 2] := by decide
private theorem tr2_9_1 : step 2 WZ.a_b_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr2_9_2 : step 2 WZ.a_bc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr2_9_3 : step 2 WZ.ab_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr2_9_4 : step 2 WZ.ac_b ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 2] := by decide
private theorem tr2_10_0 : step 2 WZ.abc ![0, 1, 2, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr2_10_1 : step 2 WZ.a_b_c ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr2_10_2 : step 2 WZ.a_bc ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr2_10_3 : step 2 WZ.ab_c ![0, 1, 2, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr2_10_4 : step 2 WZ.ac_b ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 2] := by decide
private theorem tr2_11_0 : step 2 WZ.abc ![0, 1, 2, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr2_11_1 : step 2 WZ.a_b_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 4] := by decide
private theorem tr2_11_2 : step 2 WZ.a_bc ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr2_11_3 : step 2 WZ.ab_c ![0, 1, 2, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr2_11_4 : step 2 WZ.ac_b ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 2] := by decide
private theorem tr2_12_0 : step 2 WZ.abc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 2] := by decide
private theorem tr2_12_1 : step 2 WZ.a_b_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr2_12_2 : step 2 WZ.a_bc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr2_12_3 : step 2 WZ.ab_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr2_12_4 : step 2 WZ.ac_b ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 2] := by decide
private theorem tr3_0_0 : step 3 WZ.abc ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_0_1 : step 3 WZ.a_b_c ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_0_2 : step 3 WZ.a_bc ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_0_3 : step 3 WZ.ab_c ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_0_4 : step 3 WZ.ac_b ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_1_0 : step 3 WZ.abc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_1_1 : step 3 WZ.a_b_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_1_2 : step 3 WZ.a_bc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_1_3 : step 3 WZ.ab_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_1_4 : step 3 WZ.ac_b ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_2_0 : step 3 WZ.abc ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_2_1 : step 3 WZ.a_b_c ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_2_2 : step 3 WZ.a_bc ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_2_3 : step 3 WZ.ab_c ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_2_4 : step 3 WZ.ac_b ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_3_0 : step 3 WZ.abc ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_3_1 : step 3 WZ.a_b_c ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_3_2 : step 3 WZ.a_bc ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_3_3 : step 3 WZ.ab_c ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_3_4 : step 3 WZ.ac_b ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_4_0 : step 3 WZ.abc ![0, 0, 2, 0, 2] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_4_1 : step 3 WZ.a_b_c ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_4_2 : step 3 WZ.a_bc ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 2] := by decide
private theorem tr3_4_3 : step 3 WZ.ab_c ![0, 0, 2, 0, 2] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_4_4 : step 3 WZ.ac_b ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_5_0 : step 3 WZ.abc ![0, 0, 2, 3, 2] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_5_1 : step 3 WZ.a_b_c ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_5_2 : step 3 WZ.a_bc ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 2] := by decide
private theorem tr3_5_3 : step 3 WZ.ab_c ![0, 0, 2, 3, 2] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_5_4 : step 3 WZ.ac_b ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_6_0 : step 3 WZ.abc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_6_1 : step 3 WZ.a_b_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_6_2 : step 3 WZ.a_bc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_6_3 : step 3 WZ.ab_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_6_4 : step 3 WZ.ac_b ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_7_0 : step 3 WZ.abc ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_7_1 : step 3 WZ.a_b_c ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_7_2 : step 3 WZ.a_bc ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_7_3 : step 3 WZ.ab_c ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_7_4 : step 3 WZ.ac_b ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_8_0 : step 3 WZ.abc ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_8_1 : step 3 WZ.a_b_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_8_2 : step 3 WZ.a_bc ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_8_3 : step 3 WZ.ab_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_8_4 : step 3 WZ.ac_b ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_9_0 : step 3 WZ.abc ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_9_1 : step 3 WZ.a_b_c ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_9_2 : step 3 WZ.a_bc ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_9_3 : step 3 WZ.ab_c ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_9_4 : step 3 WZ.ac_b ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_10_0 : step 3 WZ.abc ![0, 0, 2, 2, 2] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_10_1 : step 3 WZ.a_b_c ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 4] := by decide
private theorem tr3_10_2 : step 3 WZ.a_bc ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr3_10_3 : step 3 WZ.ab_c ![0, 0, 2, 2, 2] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_10_4 : step 3 WZ.ac_b ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 0] := by decide
private theorem tr3_11_0 : step 3 WZ.abc ![0, 0, 2, 3, 3] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_11_1 : step 3 WZ.a_b_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_11_2 : step 3 WZ.a_bc ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 3] := by decide
private theorem tr3_11_3 : step 3 WZ.ab_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_11_4 : step 3 WZ.ac_b ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_12_0 : step 3 WZ.abc ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 0] := by decide
private theorem tr3_12_1 : step 3 WZ.a_b_c ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr3_12_2 : step 3 WZ.a_bc ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr3_12_3 : step 3 WZ.ab_c ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr3_12_4 : step 3 WZ.ac_b ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 0] := by decide
private theorem tr3_13_0 : step 3 WZ.abc ![0, 1, 2, 2, 2] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_13_1 : step 3 WZ.a_b_c ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 4] := by decide
private theorem tr3_13_2 : step 3 WZ.a_bc ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr3_13_3 : step 3 WZ.ab_c ![0, 1, 2, 2, 2] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_13_4 : step 3 WZ.ac_b ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 1] := by decide
private theorem tr3_14_0 : step 3 WZ.abc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_14_1 : step 3 WZ.a_b_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_14_2 : step 3 WZ.a_bc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_14_3 : step 3 WZ.ab_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_14_4 : step 3 WZ.ac_b ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_15_0 : step 3 WZ.abc ![0, 1, 2, 3, 3] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_15_1 : step 3 WZ.a_b_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_15_2 : step 3 WZ.a_bc ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 3] := by decide
private theorem tr3_15_3 : step 3 WZ.ab_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_15_4 : step 3 WZ.ac_b ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_16_0 : step 3 WZ.abc ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 1] := by decide
private theorem tr3_16_1 : step 3 WZ.a_b_c ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr3_16_2 : step 3 WZ.a_bc ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr3_16_3 : step 3 WZ.ab_c ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr3_16_4 : step 3 WZ.ac_b ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 1] := by decide
private theorem tr3_17_0 : step 3 WZ.abc ![0, 1, 2, 3, 2] = ![0, 1, 1, 3, 1] := by decide
private theorem tr3_17_1 : step 3 WZ.a_b_c ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_17_2 : step 3 WZ.a_bc ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 2] := by decide
private theorem tr3_17_3 : step 3 WZ.ab_c ![0, 1, 2, 3, 2] = ![0, 1, 1, 3, 4] := by decide
private theorem tr3_17_4 : step 3 WZ.ac_b ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_18_0 : step 3 WZ.abc ![0, 1, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr3_18_1 : step 3 WZ.a_b_c ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr3_18_2 : step 3 WZ.a_bc ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr3_18_3 : step 3 WZ.ab_c ![0, 1, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr3_18_4 : step 3 WZ.ac_b ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 1] := by decide
private theorem tr3_19_0 : step 3 WZ.abc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 1] := by decide
private theorem tr3_19_1 : step 3 WZ.a_b_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr3_19_2 : step 3 WZ.a_bc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr3_19_3 : step 3 WZ.ab_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr3_19_4 : step 3 WZ.ac_b ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 1] := by decide
private theorem tr3_20_0 : step 3 WZ.abc ![0, 1, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr3_20_1 : step 3 WZ.a_b_c ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr3_20_2 : step 3 WZ.a_bc ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr3_20_3 : step 3 WZ.ab_c ![0, 1, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr3_20_4 : step 3 WZ.ac_b ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 1] := by decide
private theorem tr3_21_0 : step 3 WZ.abc ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 1] := by decide
private theorem tr3_21_1 : step 3 WZ.a_b_c ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr3_21_2 : step 3 WZ.a_bc ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr3_21_3 : step 3 WZ.ab_c ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr3_21_4 : step 3 WZ.ac_b ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 1] := by decide
private theorem tr3_22_0 : step 3 WZ.abc ![0, 1, 2, 0, 2] = ![0, 1, 1, 0, 1] := by decide
private theorem tr3_22_1 : step 3 WZ.a_b_c ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 4] := by decide
private theorem tr3_22_2 : step 3 WZ.a_bc ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 2] := by decide
private theorem tr3_22_3 : step 3 WZ.ab_c ![0, 1, 2, 0, 2] = ![0, 1, 1, 0, 4] := by decide
private theorem tr3_22_4 : step 3 WZ.ac_b ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 1] := by decide
private theorem tr3_23_0 : step 3 WZ.abc ![0, 1, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr3_23_1 : step 3 WZ.a_b_c ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 4] := by decide
private theorem tr3_23_2 : step 3 WZ.a_bc ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr3_23_3 : step 3 WZ.ab_c ![0, 1, 0, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr3_23_4 : step 3 WZ.ac_b ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 1] := by decide
private theorem tr3_24_0 : step 3 WZ.abc ![0, 1, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr3_24_1 : step 3 WZ.a_b_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_24_2 : step 3 WZ.a_bc ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 0] := by decide
private theorem tr3_24_3 : step 3 WZ.ab_c ![0, 1, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr3_24_4 : step 3 WZ.ac_b ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_25_0 : step 3 WZ.abc ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 1] := by decide
private theorem tr3_25_1 : step 3 WZ.a_b_c ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr3_25_2 : step 3 WZ.a_bc ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr3_25_3 : step 3 WZ.ab_c ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr3_25_4 : step 3 WZ.ac_b ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 1] := by decide
private theorem tr3_26_0 : step 3 WZ.abc ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_26_1 : step 3 WZ.a_b_c ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_26_2 : step 3 WZ.a_bc ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_26_3 : step 3 WZ.ab_c ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_26_4 : step 3 WZ.ac_b ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_27_0 : step 3 WZ.abc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_27_1 : step 3 WZ.a_b_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_27_2 : step 3 WZ.a_bc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_27_3 : step 3 WZ.ab_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_27_4 : step 3 WZ.ac_b ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_28_0 : step 3 WZ.abc ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_28_1 : step 3 WZ.a_b_c ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_28_2 : step 3 WZ.a_bc ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_28_3 : step 3 WZ.ab_c ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_28_4 : step 3 WZ.ac_b ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_29_0 : step 3 WZ.abc ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_29_1 : step 3 WZ.a_b_c ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_29_2 : step 3 WZ.a_bc ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_29_3 : step 3 WZ.ab_c ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_29_4 : step 3 WZ.ac_b ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_30_0 : step 3 WZ.abc ![0, 1, 2, 1, 2] = ![0, 1, 1, 1, 1] := by decide
private theorem tr3_30_1 : step 3 WZ.a_b_c ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 4] := by decide
private theorem tr3_30_2 : step 3 WZ.a_bc ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 2] := by decide
private theorem tr3_30_3 : step 3 WZ.ab_c ![0, 1, 2, 1, 2] = ![0, 1, 1, 1, 4] := by decide
private theorem tr3_30_4 : step 3 WZ.ac_b ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 1] := by decide
private theorem tr3_31_0 : step 3 WZ.abc ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr3_31_1 : step 3 WZ.a_b_c ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr3_31_2 : step 3 WZ.a_bc ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr3_31_3 : step 3 WZ.ab_c ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr3_31_4 : step 3 WZ.ac_b ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr3_32_0 : step 3 WZ.abc ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_32_1 : step 3 WZ.a_b_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_32_2 : step 3 WZ.a_bc ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_32_3 : step 3 WZ.ab_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 4] := by decide
private theorem tr3_32_4 : step 3 WZ.ac_b ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr3_33_0 : step 3 WZ.abc ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 1] := by decide
private theorem tr3_33_1 : step 3 WZ.a_b_c ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr3_33_2 : step 3 WZ.a_bc ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr3_33_3 : step 3 WZ.ab_c ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr3_33_4 : step 3 WZ.ac_b ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_0_0 : step 4 WZ.abc ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_0_1 : step 4 WZ.a_b_c ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_0_2 : step 4 WZ.a_bc ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_0_3 : step 4 WZ.ab_c ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_0_4 : step 4 WZ.ac_b ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_1_0 : step 4 WZ.abc ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_1_1 : step 4 WZ.a_b_c ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_1_2 : step 4 WZ.a_bc ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_1_3 : step 4 WZ.ab_c ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_1_4 : step 4 WZ.ac_b ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_2_0 : step 4 WZ.abc ![0, 0, 2, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_2_1 : step 4 WZ.a_b_c ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr4_2_2 : step 4 WZ.a_bc ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr4_2_3 : step 4 WZ.ab_c ![0, 0, 2, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_2_4 : step 4 WZ.ac_b ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 2] := by decide
private theorem tr4_3_0 : step 4 WZ.abc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 2] := by decide
private theorem tr4_3_1 : step 4 WZ.a_b_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr4_3_2 : step 4 WZ.a_bc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr4_3_3 : step 4 WZ.ab_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr4_3_4 : step 4 WZ.ac_b ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 2] := by decide
private theorem tr4_4_0 : step 4 WZ.abc ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 2] := by decide
private theorem tr4_4_1 : step 4 WZ.a_b_c ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 4] := by decide
private theorem tr4_4_2 : step 4 WZ.a_bc ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 2] := by decide
private theorem tr4_4_3 : step 4 WZ.ab_c ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 4] := by decide
private theorem tr4_4_4 : step 4 WZ.ac_b ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 2] := by decide
private theorem tr4_5_0 : step 4 WZ.abc ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_5_1 : step 4 WZ.a_b_c ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_5_2 : step 4 WZ.a_bc ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_5_3 : step 4 WZ.ab_c ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_5_4 : step 4 WZ.ac_b ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_6_0 : step 4 WZ.abc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_6_1 : step 4 WZ.a_b_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_6_2 : step 4 WZ.a_bc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_6_3 : step 4 WZ.ab_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_6_4 : step 4 WZ.ac_b ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_7_0 : step 4 WZ.abc ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_7_1 : step 4 WZ.a_b_c ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_7_2 : step 4 WZ.a_bc ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_7_3 : step 4 WZ.ab_c ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_7_4 : step 4 WZ.ac_b ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_8_0 : step 4 WZ.abc ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_8_1 : step 4 WZ.a_b_c ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_8_2 : step 4 WZ.a_bc ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_8_3 : step 4 WZ.ab_c ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_8_4 : step 4 WZ.ac_b ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_9_0 : step 4 WZ.abc ![0, 0, 2, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_9_1 : step 4 WZ.a_b_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_9_2 : step 4 WZ.a_bc ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr4_9_3 : step 4 WZ.ab_c ![0, 0, 2, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_9_4 : step 4 WZ.ac_b ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_10_0 : step 4 WZ.abc ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_10_1 : step 4 WZ.a_b_c ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_10_2 : step 4 WZ.a_bc ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_10_3 : step 4 WZ.ab_c ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_10_4 : step 4 WZ.ac_b ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_11_0 : step 4 WZ.abc ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_11_1 : step 4 WZ.a_b_c ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_11_2 : step 4 WZ.a_bc ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_11_3 : step 4 WZ.ab_c ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_11_4 : step 4 WZ.ac_b ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_12_0 : step 4 WZ.abc ![0, 0, 2, 2, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_12_1 : step 4 WZ.a_b_c ![0, 0, 2, 2, 0] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_12_2 : step 4 WZ.a_bc ![0, 0, 2, 2, 0] = ![0, 0, 2, 2, 0] := by decide
private theorem tr4_12_3 : step 4 WZ.ab_c ![0, 0, 2, 2, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_12_4 : step 4 WZ.ac_b ![0, 0, 2, 2, 0] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_13_0 : step 4 WZ.abc ![0, 0, 2, 3, 3] = ![0, 0, 2, 2, 2] := by decide
private theorem tr4_13_1 : step 4 WZ.a_b_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 4] := by decide
private theorem tr4_13_2 : step 4 WZ.a_bc ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 3] := by decide
private theorem tr4_13_3 : step 4 WZ.ab_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 2, 4] := by decide
private theorem tr4_13_4 : step 4 WZ.ac_b ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 2] := by decide
private theorem tr4_14_0 : step 4 WZ.abc ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_14_1 : step 4 WZ.a_b_c ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_14_2 : step 4 WZ.a_bc ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_14_3 : step 4 WZ.ab_c ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_14_4 : step 4 WZ.ac_b ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_15_0 : step 4 WZ.abc ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_15_1 : step 4 WZ.a_b_c ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_15_2 : step 4 WZ.a_bc ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_15_3 : step 4 WZ.ab_c ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_15_4 : step 4 WZ.ac_b ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_16_0 : step 4 WZ.abc ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_16_1 : step 4 WZ.a_b_c ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_16_2 : step 4 WZ.a_bc ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_16_3 : step 4 WZ.ab_c ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_16_4 : step 4 WZ.ac_b ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_17_0 : step 4 WZ.abc ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_17_1 : step 4 WZ.a_b_c ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_17_2 : step 4 WZ.a_bc ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_17_3 : step 4 WZ.ab_c ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_17_4 : step 4 WZ.ac_b ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_18_0 : step 4 WZ.abc ![0, 1, 2, 2, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_18_1 : step 4 WZ.a_b_c ![0, 1, 2, 2, 1] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_18_2 : step 4 WZ.a_bc ![0, 1, 2, 2, 1] = ![0, 1, 2, 2, 1] := by decide
private theorem tr4_18_3 : step 4 WZ.ab_c ![0, 1, 2, 2, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_18_4 : step 4 WZ.ac_b ![0, 1, 2, 2, 1] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_19_0 : step 4 WZ.abc ![0, 1, 2, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_19_1 : step 4 WZ.a_b_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_19_2 : step 4 WZ.a_bc ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr4_19_3 : step 4 WZ.ab_c ![0, 1, 2, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr4_19_4 : step 4 WZ.ac_b ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_20_0 : step 4 WZ.abc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_20_1 : step 4 WZ.a_b_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_20_2 : step 4 WZ.a_bc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_20_3 : step 4 WZ.ab_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_20_4 : step 4 WZ.ac_b ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_21_0 : step 4 WZ.abc ![0, 1, 2, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr4_21_1 : step 4 WZ.a_b_c ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr4_21_2 : step 4 WZ.a_bc ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr4_21_3 : step 4 WZ.ab_c ![0, 1, 2, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr4_21_4 : step 4 WZ.ac_b ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 2] := by decide
private theorem tr4_22_0 : step 4 WZ.abc ![0, 1, 2, 3, 3] = ![0, 1, 2, 2, 2] := by decide
private theorem tr4_22_1 : step 4 WZ.a_b_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_22_2 : step 4 WZ.a_bc ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 3] := by decide
private theorem tr4_22_3 : step 4 WZ.ab_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 2, 4] := by decide
private theorem tr4_22_4 : step 4 WZ.ac_b ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_23_0 : step 4 WZ.abc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 2] := by decide
private theorem tr4_23_1 : step 4 WZ.a_b_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr4_23_2 : step 4 WZ.a_bc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr4_23_3 : step 4 WZ.ab_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr4_23_4 : step 4 WZ.ac_b ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 2] := by decide
private theorem tr4_24_0 : step 4 WZ.abc ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_24_1 : step 4 WZ.a_b_c ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr4_24_2 : step 4 WZ.a_bc ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_24_3 : step 4 WZ.ab_c ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr4_24_4 : step 4 WZ.ac_b ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_25_0 : step 4 WZ.abc ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_25_1 : step 4 WZ.a_b_c ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_25_2 : step 4 WZ.a_bc ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_25_3 : step 4 WZ.ab_c ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_25_4 : step 4 WZ.ac_b ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_26_0 : step 4 WZ.abc ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_26_1 : step 4 WZ.a_b_c ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr4_26_2 : step 4 WZ.a_bc ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr4_26_3 : step 4 WZ.ab_c ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr4_26_4 : step 4 WZ.ac_b ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 1] := by decide
private theorem tr4_27_0 : step 4 WZ.abc ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_27_1 : step 4 WZ.a_b_c ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_27_2 : step 4 WZ.a_bc ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_27_3 : step 4 WZ.ab_c ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_27_4 : step 4 WZ.ac_b ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_28_0 : step 4 WZ.abc ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_28_1 : step 4 WZ.a_b_c ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_28_2 : step 4 WZ.a_bc ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_28_3 : step 4 WZ.ab_c ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_28_4 : step 4 WZ.ac_b ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_29_0 : step 4 WZ.abc ![0, 1, 0, 0, 1] = ![0, 0, 0, 0, 0] := by decide
private theorem tr4_29_1 : step 4 WZ.a_b_c ![0, 1, 0, 0, 1] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_29_2 : step 4 WZ.a_bc ![0, 1, 0, 0, 1] = ![0, 1, 0, 0, 1] := by decide
private theorem tr4_29_3 : step 4 WZ.ab_c ![0, 1, 0, 0, 1] = ![0, 0, 0, 0, 4] := by decide
private theorem tr4_29_4 : step 4 WZ.ac_b ![0, 1, 0, 0, 1] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_30_0 : step 4 WZ.abc ![0, 1, 2, 0, 1] = ![0, 1, 1, 0, 1] := by decide
private theorem tr4_30_1 : step 4 WZ.a_b_c ![0, 1, 2, 0, 1] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_30_2 : step 4 WZ.a_bc ![0, 1, 2, 0, 1] = ![0, 1, 2, 0, 1] := by decide
private theorem tr4_30_3 : step 4 WZ.ab_c ![0, 1, 2, 0, 1] = ![0, 1, 1, 0, 4] := by decide
private theorem tr4_30_4 : step 4 WZ.ac_b ![0, 1, 2, 0, 1] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_31_0 : step 4 WZ.abc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_31_1 : step 4 WZ.a_b_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_31_2 : step 4 WZ.a_bc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_31_3 : step 4 WZ.ab_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_31_4 : step 4 WZ.ac_b ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_32_0 : step 4 WZ.abc ![0, 1, 2, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr4_32_1 : step 4 WZ.a_b_c ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_32_2 : step 4 WZ.a_bc ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr4_32_3 : step 4 WZ.ab_c ![0, 1, 2, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr4_32_4 : step 4 WZ.ac_b ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_33_0 : step 4 WZ.abc ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 1] := by decide
private theorem tr4_33_1 : step 4 WZ.a_b_c ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 4] := by decide
private theorem tr4_33_2 : step 4 WZ.a_bc ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 1] := by decide
private theorem tr4_33_3 : step 4 WZ.ab_c ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 4] := by decide
private theorem tr4_33_4 : step 4 WZ.ac_b ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 1] := by decide
private theorem tr4_34_0 : step 4 WZ.abc ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_34_1 : step 4 WZ.a_b_c ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_34_2 : step 4 WZ.a_bc ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_34_3 : step 4 WZ.ab_c ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 4] := by decide
private theorem tr4_34_4 : step 4 WZ.ac_b ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 2] := by decide
private theorem tr4_35_0 : step 4 WZ.abc ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 1] := by decide
private theorem tr4_35_1 : step 4 WZ.a_b_c ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 4] := by decide
private theorem tr4_35_2 : step 4 WZ.a_bc ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 4] := by decide
private theorem tr4_35_3 : step 4 WZ.ab_c ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 4] := by decide
private theorem tr4_35_4 : step 4 WZ.ac_b ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 1] := by decide
private theorem tr4_36_0 : step 4 WZ.abc ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_36_1 : step 4 WZ.a_b_c ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_36_2 : step 4 WZ.a_bc ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_36_3 : step 4 WZ.ab_c ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_36_4 : step 4 WZ.ac_b ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_37_0 : step 4 WZ.abc ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_37_1 : step 4 WZ.a_b_c ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_37_2 : step 4 WZ.a_bc ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_37_3 : step 4 WZ.ab_c ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_37_4 : step 4 WZ.ac_b ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_38_0 : step 4 WZ.abc ![0, 1, 0, 3, 1] = ![0, 0, 0, 3, 0] := by decide
private theorem tr4_38_1 : step 4 WZ.a_b_c ![0, 1, 0, 3, 1] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_38_2 : step 4 WZ.a_bc ![0, 1, 0, 3, 1] = ![0, 1, 0, 3, 1] := by decide
private theorem tr4_38_3 : step 4 WZ.ab_c ![0, 1, 0, 3, 1] = ![0, 0, 0, 3, 4] := by decide
private theorem tr4_38_4 : step 4 WZ.ac_b ![0, 1, 0, 3, 1] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_39_0 : step 4 WZ.abc ![0, 1, 2, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr4_39_1 : step 4 WZ.a_b_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 4] := by decide
private theorem tr4_39_2 : step 4 WZ.a_bc ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 0] := by decide
private theorem tr4_39_3 : step 4 WZ.ab_c ![0, 1, 2, 3, 0] = ![0, 1, 0, 3, 4] := by decide
private theorem tr4_39_4 : step 4 WZ.ac_b ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 2] := by decide
private theorem tr4_40_0 : step 4 WZ.abc ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 2] := by decide
private theorem tr4_40_1 : step 4 WZ.a_b_c ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 4] := by decide
private theorem tr4_40_2 : step 4 WZ.a_bc ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 2] := by decide
private theorem tr4_40_3 : step 4 WZ.ab_c ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 4] := by decide
private theorem tr4_40_4 : step 4 WZ.ac_b ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 2] := by decide
private theorem tr5_0_0 : step 5 WZ.abc ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_0_1 : step 5 WZ.a_b_c ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_0_2 : step 5 WZ.a_bc ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_0_3 : step 5 WZ.ab_c ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_0_4 : step 5 WZ.ac_b ![0, 0, 0, 0, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_1_0 : step 5 WZ.abc ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_1_1 : step 5 WZ.a_b_c ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_1_2 : step 5 WZ.a_bc ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_1_3 : step 5 WZ.ab_c ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_1_4 : step 5 WZ.ac_b ![0, 0, 0, 0, 4] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_2_0 : step 5 WZ.abc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_2_1 : step 5 WZ.a_b_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_2_2 : step 5 WZ.a_bc ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_2_3 : step 5 WZ.ab_c ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_2_4 : step 5 WZ.ac_b ![0, 0, 2, 0, 4] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_3_0 : step 5 WZ.abc ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_3_1 : step 5 WZ.a_b_c ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_3_2 : step 5 WZ.a_bc ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_3_3 : step 5 WZ.ab_c ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_3_4 : step 5 WZ.ac_b ![0, 0, 2, 0, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_4_0 : step 5 WZ.abc ![0, 0, 2, 0, 2] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_4_1 : step 5 WZ.a_b_c ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_4_2 : step 5 WZ.a_bc ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 2] := by decide
private theorem tr5_4_3 : step 5 WZ.ab_c ![0, 0, 2, 0, 2] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_4_4 : step 5 WZ.ac_b ![0, 0, 2, 0, 2] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_5_0 : step 5 WZ.abc ![0, 0, 0, 3, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_5_1 : step 5 WZ.a_b_c ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 4] := by decide
private theorem tr5_5_2 : step 5 WZ.a_bc ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 0] := by decide
private theorem tr5_5_3 : step 5 WZ.ab_c ![0, 0, 0, 3, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_5_4 : step 5 WZ.ac_b ![0, 0, 0, 3, 0] = ![0, 0, 0, 3, 3] := by decide
private theorem tr5_6_0 : step 5 WZ.abc ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 3] := by decide
private theorem tr5_6_1 : step 5 WZ.a_b_c ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr5_6_2 : step 5 WZ.a_bc ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr5_6_3 : step 5 WZ.ab_c ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 4] := by decide
private theorem tr5_6_4 : step 5 WZ.ac_b ![0, 0, 0, 3, 4] = ![0, 0, 0, 3, 3] := by decide
private theorem tr5_7_0 : step 5 WZ.abc ![0, 0, 2, 3, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_7_1 : step 5 WZ.a_b_c ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_7_2 : step 5 WZ.a_bc ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 2] := by decide
private theorem tr5_7_3 : step 5 WZ.ab_c ![0, 0, 2, 3, 2] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_7_4 : step 5 WZ.ac_b ![0, 0, 2, 3, 2] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_8_0 : step 5 WZ.abc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_8_1 : step 5 WZ.a_b_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_8_2 : step 5 WZ.a_bc ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_8_3 : step 5 WZ.ab_c ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_8_4 : step 5 WZ.ac_b ![0, 0, 2, 3, 4] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_9_0 : step 5 WZ.abc ![0, 0, 2, 3, 0] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_9_1 : step 5 WZ.a_b_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_9_2 : step 5 WZ.a_bc ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 0] := by decide
private theorem tr5_9_3 : step 5 WZ.ab_c ![0, 0, 2, 3, 0] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_9_4 : step 5 WZ.ac_b ![0, 0, 2, 3, 0] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_10_0 : step 5 WZ.abc ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_10_1 : step 5 WZ.a_b_c ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_10_2 : step 5 WZ.a_bc ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_10_3 : step 5 WZ.ab_c ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_10_4 : step 5 WZ.ac_b ![0, 0, 2, 2, 2] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_11_0 : step 5 WZ.abc ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_11_1 : step 5 WZ.a_b_c ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_11_2 : step 5 WZ.a_bc ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_11_3 : step 5 WZ.ab_c ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_11_4 : step 5 WZ.ac_b ![0, 0, 2, 2, 4] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_12_0 : step 5 WZ.abc ![0, 0, 2, 2, 0] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_12_1 : step 5 WZ.a_b_c ![0, 0, 2, 2, 0] = ![0, 0, 2, 2, 4] := by decide
private theorem tr5_12_2 : step 5 WZ.a_bc ![0, 0, 2, 2, 0] = ![0, 0, 2, 2, 0] := by decide
private theorem tr5_12_3 : step 5 WZ.ab_c ![0, 0, 2, 2, 0] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_12_4 : step 5 WZ.ac_b ![0, 0, 2, 2, 0] = ![0, 0, 2, 2, 2] := by decide
private theorem tr5_13_0 : step 5 WZ.abc ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_13_1 : step 5 WZ.a_b_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_13_2 : step 5 WZ.a_bc ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_13_3 : step 5 WZ.ab_c ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 4] := by decide
private theorem tr5_13_4 : step 5 WZ.ac_b ![0, 0, 2, 3, 3] = ![0, 0, 2, 3, 3] := by decide
private theorem tr5_14_0 : step 5 WZ.abc ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_14_1 : step 5 WZ.a_b_c ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_14_2 : step 5 WZ.a_bc ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_14_3 : step 5 WZ.ab_c ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_14_4 : step 5 WZ.ac_b ![0, 1, 1, 1, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_15_0 : step 5 WZ.abc ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_15_1 : step 5 WZ.a_b_c ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_15_2 : step 5 WZ.a_bc ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_15_3 : step 5 WZ.ab_c ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_15_4 : step 5 WZ.ac_b ![0, 1, 1, 1, 4] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_16_0 : step 5 WZ.abc ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_16_1 : step 5 WZ.a_b_c ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_16_2 : step 5 WZ.a_bc ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_16_3 : step 5 WZ.ab_c ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_16_4 : step 5 WZ.ac_b ![0, 1, 2, 2, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_17_0 : step 5 WZ.abc ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_17_1 : step 5 WZ.a_b_c ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_17_2 : step 5 WZ.a_bc ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_17_3 : step 5 WZ.ab_c ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_17_4 : step 5 WZ.ac_b ![0, 1, 2, 2, 4] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_18_0 : step 5 WZ.abc ![0, 1, 2, 2, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_18_1 : step 5 WZ.a_b_c ![0, 1, 2, 2, 1] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_18_2 : step 5 WZ.a_bc ![0, 1, 2, 2, 1] = ![0, 1, 2, 2, 1] := by decide
private theorem tr5_18_3 : step 5 WZ.ab_c ![0, 1, 2, 2, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_18_4 : step 5 WZ.ac_b ![0, 1, 2, 2, 1] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_19_0 : step 5 WZ.abc ![0, 1, 1, 3, 1] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_19_1 : step 5 WZ.a_b_c ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 4] := by decide
private theorem tr5_19_2 : step 5 WZ.a_bc ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 1] := by decide
private theorem tr5_19_3 : step 5 WZ.ab_c ![0, 1, 1, 3, 1] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_19_4 : step 5 WZ.ac_b ![0, 1, 1, 3, 1] = ![0, 1, 1, 3, 3] := by decide
private theorem tr5_20_0 : step 5 WZ.abc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_20_1 : step 5 WZ.a_b_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_20_2 : step 5 WZ.a_bc ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_20_3 : step 5 WZ.ab_c ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_20_4 : step 5 WZ.ac_b ![0, 1, 2, 3, 4] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_21_0 : step 5 WZ.abc ![0, 1, 2, 3, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_21_1 : step 5 WZ.a_b_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_21_2 : step 5 WZ.a_bc ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 1] := by decide
private theorem tr5_21_3 : step 5 WZ.ab_c ![0, 1, 2, 3, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_21_4 : step 5 WZ.ac_b ![0, 1, 2, 3, 1] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_22_0 : step 5 WZ.abc ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 3] := by decide
private theorem tr5_22_1 : step 5 WZ.a_b_c ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr5_22_2 : step 5 WZ.a_bc ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr5_22_3 : step 5 WZ.ab_c ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 4] := by decide
private theorem tr5_22_4 : step 5 WZ.ac_b ![0, 1, 1, 3, 4] = ![0, 1, 1, 3, 3] := by decide
private theorem tr5_23_0 : step 5 WZ.abc ![0, 1, 2, 3, 2] = ![0, 1, 2, 2, 2] := by decide
private theorem tr5_23_1 : step 5 WZ.a_b_c ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_23_2 : step 5 WZ.a_bc ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 2] := by decide
private theorem tr5_23_3 : step 5 WZ.ab_c ![0, 1, 2, 3, 2] = ![0, 1, 2, 2, 4] := by decide
private theorem tr5_23_4 : step 5 WZ.ac_b ![0, 1, 2, 3, 2] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_24_0 : step 5 WZ.abc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_24_1 : step 5 WZ.a_b_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_24_2 : step 5 WZ.a_bc ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_24_3 : step 5 WZ.ab_c ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_24_4 : step 5 WZ.ac_b ![0, 1, 2, 1, 4] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_25_0 : step 5 WZ.abc ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_25_1 : step 5 WZ.a_b_c ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_25_2 : step 5 WZ.a_bc ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_25_3 : step 5 WZ.ab_c ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_25_4 : step 5 WZ.ac_b ![0, 1, 2, 1, 1] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_26_0 : step 5 WZ.abc ![0, 1, 2, 1, 2] = ![0, 1, 1, 1, 1] := by decide
private theorem tr5_26_1 : step 5 WZ.a_b_c ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 4] := by decide
private theorem tr5_26_2 : step 5 WZ.a_bc ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 2] := by decide
private theorem tr5_26_3 : step 5 WZ.ab_c ![0, 1, 2, 1, 2] = ![0, 1, 1, 1, 4] := by decide
private theorem tr5_26_4 : step 5 WZ.ac_b ![0, 1, 2, 1, 2] = ![0, 1, 2, 1, 1] := by decide
private theorem tr5_27_0 : step 5 WZ.abc ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_27_1 : step 5 WZ.a_b_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_27_2 : step 5 WZ.a_bc ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_27_3 : step 5 WZ.ab_c ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_27_4 : step 5 WZ.ac_b ![0, 1, 2, 3, 3] = ![0, 1, 2, 3, 3] := by decide
private theorem tr5_28_0 : step 5 WZ.abc ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_28_1 : step 5 WZ.a_b_c ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_28_2 : step 5 WZ.a_bc ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_28_3 : step 5 WZ.ab_c ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_28_4 : step 5 WZ.ac_b ![0, 1, 0, 0, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_29_0 : step 5 WZ.abc ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_29_1 : step 5 WZ.a_b_c ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_29_2 : step 5 WZ.a_bc ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_29_3 : step 5 WZ.ab_c ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_29_4 : step 5 WZ.ac_b ![0, 1, 0, 0, 4] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_30_0 : step 5 WZ.abc ![0, 1, 0, 0, 1] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_30_1 : step 5 WZ.a_b_c ![0, 1, 0, 0, 1] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_30_2 : step 5 WZ.a_bc ![0, 1, 0, 0, 1] = ![0, 1, 0, 0, 1] := by decide
private theorem tr5_30_3 : step 5 WZ.ab_c ![0, 1, 0, 0, 1] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_30_4 : step 5 WZ.ac_b ![0, 1, 0, 0, 1] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_31_0 : step 5 WZ.abc ![0, 1, 1, 0, 1] = ![0, 0, 0, 0, 0] := by decide
private theorem tr5_31_1 : step 5 WZ.a_b_c ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 4] := by decide
private theorem tr5_31_2 : step 5 WZ.a_bc ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 1] := by decide
private theorem tr5_31_3 : step 5 WZ.ab_c ![0, 1, 1, 0, 1] = ![0, 0, 0, 0, 4] := by decide
private theorem tr5_31_4 : step 5 WZ.ac_b ![0, 1, 1, 0, 1] = ![0, 1, 1, 0, 0] := by decide
private theorem tr5_32_0 : step 5 WZ.abc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_32_1 : step 5 WZ.a_b_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_32_2 : step 5 WZ.a_bc ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_32_3 : step 5 WZ.ab_c ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_32_4 : step 5 WZ.ac_b ![0, 1, 2, 0, 4] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_33_0 : step 5 WZ.abc ![0, 1, 2, 0, 1] = ![0, 0, 2, 0, 0] := by decide
private theorem tr5_33_1 : step 5 WZ.a_b_c ![0, 1, 2, 0, 1] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_33_2 : step 5 WZ.a_bc ![0, 1, 2, 0, 1] = ![0, 1, 2, 0, 1] := by decide
private theorem tr5_33_3 : step 5 WZ.ab_c ![0, 1, 2, 0, 1] = ![0, 0, 2, 0, 4] := by decide
private theorem tr5_33_4 : step 5 WZ.ac_b ![0, 1, 2, 0, 1] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_34_0 : step 5 WZ.abc ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 0] := by decide
private theorem tr5_34_1 : step 5 WZ.a_b_c ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 4] := by decide
private theorem tr5_34_2 : step 5 WZ.a_bc ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 4] := by decide
private theorem tr5_34_3 : step 5 WZ.ab_c ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 4] := by decide
private theorem tr5_34_4 : step 5 WZ.ac_b ![0, 1, 1, 0, 4] = ![0, 1, 1, 0, 0] := by decide
private theorem tr5_35_0 : step 5 WZ.abc ![0, 1, 2, 0, 2] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_35_1 : step 5 WZ.a_b_c ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_35_2 : step 5 WZ.a_bc ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 2] := by decide
private theorem tr5_35_3 : step 5 WZ.ab_c ![0, 1, 2, 0, 2] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_35_4 : step 5 WZ.ac_b ![0, 1, 2, 0, 2] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_36_0 : step 5 WZ.abc ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_36_1 : step 5 WZ.a_b_c ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_36_2 : step 5 WZ.a_bc ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_36_3 : step 5 WZ.ab_c ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_36_4 : step 5 WZ.ac_b ![0, 1, 2, 0, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_37_0 : step 5 WZ.abc ![0, 1, 0, 3, 0] = ![0, 1, 0, 0, 0] := by decide
private theorem tr5_37_1 : step 5 WZ.a_b_c ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 4] := by decide
private theorem tr5_37_2 : step 5 WZ.a_bc ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 0] := by decide
private theorem tr5_37_3 : step 5 WZ.ab_c ![0, 1, 0, 3, 0] = ![0, 1, 0, 0, 4] := by decide
private theorem tr5_37_4 : step 5 WZ.ac_b ![0, 1, 0, 3, 0] = ![0, 1, 0, 3, 3] := by decide
private theorem tr5_38_0 : step 5 WZ.abc ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 3] := by decide
private theorem tr5_38_1 : step 5 WZ.a_b_c ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr5_38_2 : step 5 WZ.a_bc ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr5_38_3 : step 5 WZ.ab_c ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 4] := by decide
private theorem tr5_38_4 : step 5 WZ.ac_b ![0, 1, 0, 3, 4] = ![0, 1, 0, 3, 3] := by decide
private theorem tr5_39_0 : step 5 WZ.abc ![0, 1, 0, 3, 1] = ![0, 1, 0, 1, 1] := by decide
private theorem tr5_39_1 : step 5 WZ.a_b_c ![0, 1, 0, 3, 1] = ![0, 1, 0, 3, 4] := by decide
private theorem tr5_39_2 : step 5 WZ.a_bc ![0, 1, 0, 3, 1] = ![0, 1, 0, 3, 1] := by decide
private theorem tr5_39_3 : step 5 WZ.ab_c ![0, 1, 0, 3, 1] = ![0, 1, 0, 1, 4] := by decide
private theorem tr5_39_4 : step 5 WZ.ac_b ![0, 1, 0, 3, 1] = ![0, 1, 0, 3, 3] := by decide
private theorem tr5_40_0 : step 5 WZ.abc ![0, 1, 2, 3, 0] = ![0, 1, 2, 0, 0] := by decide
private theorem tr5_40_1 : step 5 WZ.a_b_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 4] := by decide
private theorem tr5_40_2 : step 5 WZ.a_bc ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 0] := by decide
private theorem tr5_40_3 : step 5 WZ.ab_c ![0, 1, 2, 3, 0] = ![0, 1, 2, 0, 4] := by decide
private theorem tr5_40_4 : step 5 WZ.ac_b ![0, 1, 2, 3, 0] = ![0, 1, 2, 3, 3] := by decide

/-! ## Collapsing the sum one hyperedge at a time -/
private theorem stg0 (P : WZ → ℚ) (G : St → ℚ) :
    G stInit = v0_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0] := by
  simp only [v0_0, stInit]; ring
private theorem stg1 (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t0 : WZ, P t0 * (G (step 0 t0 (stInit))))
      = v1_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 0]
      + v1_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 4]
      + v1_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0]
      + v1_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 4]
      + v1_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 1] := by
  have h : (∑ t0 : WZ, P t0 * (G (step 0 t0 (stInit))))
      = v0_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 0 t ![0, 1, 2, 3, 0])) :=
    stg0 P (fun s => ∑ t : WZ, P t * G (step 0 t s))
  rw [h]
  simp only [sum_wz]
  rw [tr0_0_0, tr0_0_3, tr0_0_4, tr0_0_2, tr0_0_1, ← hsym]
  rw [q1_0, q1_1, q1_2, q1_3, q1_4]
  ring
private theorem stg2 (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (G (step 1 t1 (step 0 t0 (stInit))))))
      = v2_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 0]
      + v2_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 4]
      + v2_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 0]
      + v2_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 4]
      + v2_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 3]
      + v2_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 3]
      + v2_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 4]
      + v2_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 0]
      + v2_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0]
      + v2_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 4]
      + v2_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 1]
      + v2_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 1]
      + v2_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 4] := by
  have h : (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (G (step 1 t1 (step 0 t0 (stInit))))))
      = v1_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 1 t ![0, 0, 2, 3, 0]))
      + v1_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 1 t ![0, 1, 2, 3, 4]))
      + v1_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 1 t ![0, 1, 2, 3, 0]))
      + v1_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 1 t ![0, 0, 2, 3, 4]))
      + v1_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 1 t ![0, 1, 2, 3, 1])) :=
    stg1 P hsym (fun s => ∑ t : WZ, P t * G (step 1 t s))
  rw [h]
  simp only [sum_wz]
  rw [tr1_0_0, tr1_0_3, tr1_0_4, tr1_0_2, tr1_0_1, tr1_1_0, tr1_1_3, tr1_1_4, tr1_1_2, tr1_1_1, tr1_2_0, tr1_2_3, tr1_2_4, tr1_2_2, tr1_2_1, tr1_3_0, tr1_3_3, tr1_3_4, tr1_3_2, tr1_3_1, tr1_4_0, tr1_4_3, tr1_4_4, tr1_4_2, tr1_4_1, ← hsym]
  rw [q2_0, q2_1, q2_2, q2_3, q2_4, q2_5, q2_6, q2_7, q2_8, q2_9, q2_10, q2_11, q2_12]
  ring
private theorem stg3 (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (G (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))
      = v3_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 0]
      + v3_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 4]
      + v3_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 0]
      + v3_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 4]
      + v3_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 2]
      + v3_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 2]
      + v3_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 4]
      + v3_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 0]
      + v3_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 0]
      + v3_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 4]
      + v3_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 2]
      + v3_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 3]
      + v3_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 4]
      + v3_13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 2]
      + v3_14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 4]
      + v3_15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 3]
      + v3_16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 4]
      + v3_17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 2]
      + v3_18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 0]
      + v3_19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 4]
      + v3_20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 0]
      + v3_21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 4]
      + v3_22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 2]
      + v3_23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 0]
      + v3_24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0]
      + v3_25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 4]
      + v3_26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 1]
      + v3_27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 4]
      + v3_28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 1]
      + v3_29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 4]
      + v3_30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 2]
      + v3_31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 1]
      + v3_32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 1]
      + v3_33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 4] := by
  have h : (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (G (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))
      = v2_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 0, 2, 0, 0]))
      + v2_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 0, 2, 3, 4]))
      + v2_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 0, 2, 3, 0]))
      + v2_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 0, 2, 0, 4]))
      + v2_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 0, 2, 3, 3]))
      + v2_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 3, 3]))
      + v2_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 3, 4]))
      + v2_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 0, 0]))
      + v2_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 3, 0]))
      + v2_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 0, 4]))
      + v2_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 1, 1]))
      + v2_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 3, 1]))
      + v2_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 2 t ![0, 1, 2, 1, 4])) :=
    stg2 P hsym (fun s => ∑ t : WZ, P t * G (step 2 t s))
  rw [h]
  simp only [sum_wz]
  rw [tr2_0_0, tr2_0_3, tr2_0_4, tr2_0_2, tr2_0_1, tr2_1_0, tr2_1_3, tr2_1_4, tr2_1_2, tr2_1_1, tr2_2_0, tr2_2_3, tr2_2_4, tr2_2_2, tr2_2_1, tr2_3_0, tr2_3_3, tr2_3_4, tr2_3_2, tr2_3_1, tr2_4_0, tr2_4_3, tr2_4_4, tr2_4_2, tr2_4_1, tr2_5_0, tr2_5_3, tr2_5_4, tr2_5_2, tr2_5_1, tr2_6_0, tr2_6_3, tr2_6_4, tr2_6_2, tr2_6_1, tr2_7_0, tr2_7_3, tr2_7_4, tr2_7_2, tr2_7_1, tr2_8_0, tr2_8_3, tr2_8_4, tr2_8_2, tr2_8_1, tr2_9_0, tr2_9_3, tr2_9_4, tr2_9_2, tr2_9_1, tr2_10_0, tr2_10_3, tr2_10_4, tr2_10_2, tr2_10_1, tr2_11_0, tr2_11_3, tr2_11_4, tr2_11_2, tr2_11_1, tr2_12_0, tr2_12_3, tr2_12_4, tr2_12_2, tr2_12_1, ← hsym]
  rw [q3_0, q3_1, q3_2, q3_3, q3_4, q3_5, q3_6, q3_7, q3_8, q3_9, q3_10, q3_11, q3_12, q3_13, q3_14, q3_15, q3_16, q3_17, q3_18, q3_19, q3_20, q3_21, q3_22, q3_23, q3_24, q3_25, q3_26, q3_27, q3_28, q3_29, q3_30, q3_31, q3_32, q3_33]
  ring
private theorem stg4 (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (G (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))))
      = v4_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 0]
      + v4_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 4]
      + v4_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 0]
      + v4_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 4]
      + v4_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 2]
      + v4_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 0]
      + v4_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 4]
      + v4_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 2]
      + v4_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 4]
      + v4_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 0]
      + v4_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 4]
      + v4_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 2]
      + v4_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 0]
      + v4_13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 3]
      + v4_14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 1]
      + v4_15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 4]
      + v4_16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 2]
      + v4_17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 4]
      + v4_18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 1]
      + v4_19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 1]
      + v4_20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 4]
      + v4_21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 1]
      + v4_22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 3]
      + v4_23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 4]
      + v4_24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 1]
      + v4_25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 2]
      + v4_26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 4]
      + v4_27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 4]
      + v4_28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 0]
      + v4_29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 1]
      + v4_30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 1]
      + v4_31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 4]
      + v4_32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 0]
      + v4_33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 1]
      + v4_34 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 2]
      + v4_35 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 4]
      + v4_36 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 4]
      + v4_37 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 0]
      + v4_38 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 1]
      + v4_39 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0]
      + v4_40 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 2] := by
  have h : (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (G (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))))
      = v3_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 0, 0, 0]))
      + v3_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 0, 4]))
      + v3_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 0, 0]))
      + v3_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 0, 0, 4]))
      + v3_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 0, 2]))
      + v3_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 3, 2]))
      + v3_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 3, 4]))
      + v3_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 0, 3, 0]))
      + v3_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 3, 0]))
      + v3_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 0, 3, 4]))
      + v3_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 2, 2]))
      + v3_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 3, 3]))
      + v3_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 0, 2, 2, 4]))
      + v3_13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 2, 2]))
      + v3_14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 3, 4]))
      + v3_15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 3, 3]))
      + v3_16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 2, 4]))
      + v3_17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 3, 2]))
      + v3_18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 0, 0, 0]))
      + v3_19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 0, 4]))
      + v3_20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 0, 0]))
      + v3_21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 0, 0, 4]))
      + v3_22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 0, 2]))
      + v3_23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 0, 3, 0]))
      + v3_24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 3, 0]))
      + v3_25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 0, 3, 4]))
      + v3_26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 1, 1, 1]))
      + v3_27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 1, 4]))
      + v3_28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 1, 1]))
      + v3_29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 1, 1, 4]))
      + v3_30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 1, 2]))
      + v3_31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 1, 3, 1]))
      + v3_32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 2, 3, 1]))
      + v3_33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 3 t ![0, 1, 1, 3, 4])) :=
    stg3 P hsym (fun s => ∑ t : WZ, P t * G (step 3 t s))
  rw [h]
  simp only [sum_wz]
  rw [tr3_0_0, tr3_0_3, tr3_0_4, tr3_0_2, tr3_0_1, tr3_1_0, tr3_1_3, tr3_1_4, tr3_1_2, tr3_1_1, tr3_2_0, tr3_2_3, tr3_2_4, tr3_2_2, tr3_2_1, tr3_3_0, tr3_3_3, tr3_3_4, tr3_3_2, tr3_3_1, tr3_4_0, tr3_4_3, tr3_4_4, tr3_4_2, tr3_4_1, tr3_5_0, tr3_5_3, tr3_5_4, tr3_5_2, tr3_5_1, tr3_6_0, tr3_6_3, tr3_6_4, tr3_6_2, tr3_6_1, tr3_7_0, tr3_7_3, tr3_7_4, tr3_7_2, tr3_7_1, tr3_8_0, tr3_8_3, tr3_8_4, tr3_8_2, tr3_8_1, tr3_9_0, tr3_9_3, tr3_9_4, tr3_9_2, tr3_9_1, tr3_10_0, tr3_10_3, tr3_10_4, tr3_10_2, tr3_10_1, tr3_11_0, tr3_11_3, tr3_11_4, tr3_11_2, tr3_11_1, tr3_12_0, tr3_12_3, tr3_12_4, tr3_12_2, tr3_12_1, tr3_13_0, tr3_13_3, tr3_13_4, tr3_13_2, tr3_13_1, tr3_14_0, tr3_14_3, tr3_14_4, tr3_14_2, tr3_14_1, tr3_15_0, tr3_15_3, tr3_15_4, tr3_15_2, tr3_15_1, tr3_16_0, tr3_16_3, tr3_16_4, tr3_16_2, tr3_16_1, tr3_17_0, tr3_17_3, tr3_17_4, tr3_17_2, tr3_17_1, tr3_18_0, tr3_18_3, tr3_18_4, tr3_18_2, tr3_18_1, tr3_19_0, tr3_19_3, tr3_19_4, tr3_19_2, tr3_19_1, tr3_20_0, tr3_20_3, tr3_20_4, tr3_20_2, tr3_20_1, tr3_21_0, tr3_21_3, tr3_21_4, tr3_21_2, tr3_21_1, tr3_22_0, tr3_22_3, tr3_22_4, tr3_22_2, tr3_22_1, tr3_23_0, tr3_23_3, tr3_23_4, tr3_23_2, tr3_23_1, tr3_24_0, tr3_24_3, tr3_24_4, tr3_24_2, tr3_24_1, tr3_25_0, tr3_25_3, tr3_25_4, tr3_25_2, tr3_25_1, tr3_26_0, tr3_26_3, tr3_26_4, tr3_26_2, tr3_26_1, tr3_27_0, tr3_27_3, tr3_27_4, tr3_27_2, tr3_27_1, tr3_28_0, tr3_28_3, tr3_28_4, tr3_28_2, tr3_28_1, tr3_29_0, tr3_29_3, tr3_29_4, tr3_29_2, tr3_29_1, tr3_30_0, tr3_30_3, tr3_30_4, tr3_30_2, tr3_30_1, tr3_31_0, tr3_31_3, tr3_31_4, tr3_31_2, tr3_31_1, tr3_32_0, tr3_32_3, tr3_32_4, tr3_32_2, tr3_32_1, tr3_33_0, tr3_33_3, tr3_33_4, tr3_33_2, tr3_33_1, ← hsym]
  rw [q4_0, q4_1, q4_2, q4_3, q4_4, q4_5, q4_6, q4_7, q4_8, q4_9, q4_10, q4_11, q4_12, q4_13, q4_14, q4_15, q4_16, q4_17, q4_18, q4_19, q4_20, q4_21, q4_22, q4_23, q4_24, q4_25, q4_26, q4_27, q4_28, q4_29, q4_30, q4_31, q4_32, q4_33, q4_34, q4_35, q4_36, q4_37, q4_38, q4_39, q4_40]
  ring
private theorem stg5 (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (∑ t4 : WZ, P t4 * (G (step 4 t4 (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))))))
      = v5_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 0]
      + v5_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 4]
      + v5_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 4]
      + v5_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 0]
      + v5_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 2]
      + v5_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 0]
      + v5_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 4]
      + v5_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 2]
      + v5_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 4]
      + v5_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 0]
      + v5_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 2]
      + v5_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 4]
      + v5_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 0]
      + v5_13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 3]
      + v5_14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 1]
      + v5_15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 4]
      + v5_16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 2]
      + v5_17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 4]
      + v5_18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 1]
      + v5_19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 1]
      + v5_20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 4]
      + v5_21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 1]
      + v5_22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 4]
      + v5_23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 2]
      + v5_24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 4]
      + v5_25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 1]
      + v5_26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 2]
      + v5_27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 3]
      + v5_28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 0]
      + v5_29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 4]
      + v5_30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 1]
      + v5_31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 1]
      + v5_32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 4]
      + v5_33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 1]
      + v5_34 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 4]
      + v5_35 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 2]
      + v5_36 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 0]
      + v5_37 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 0]
      + v5_38 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 4]
      + v5_39 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 1]
      + v5_40 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0] := by
  have h : (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (∑ t4 : WZ, P t4 * (G (step 4 t4 (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))))))
      = v4_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 0, 0, 0]))
      + v4_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 0, 0, 4]))
      + v4_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 0, 0]))
      + v4_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 0, 4]))
      + v4_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 0, 2]))
      + v4_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 0, 3, 0]))
      + v4_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 3, 4]))
      + v4_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 3, 2]))
      + v4_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 0, 3, 4]))
      + v4_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 3, 0]))
      + v4_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 2, 4]))
      + v4_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 2, 2]))
      + v4_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 2, 0]))
      + v4_13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 0, 2, 3, 3]))
      + v4_14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 1, 1, 1]))
      + v4_15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 2, 4]))
      + v4_16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 2, 2]))
      + v4_17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 1, 1, 4]))
      + v4_18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 2, 1]))
      + v4_19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 3, 1]))
      + v4_20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 3, 4]))
      + v4_21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 1, 1]))
      + v4_22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 3, 3]))
      + v4_23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 1, 4]))
      + v4_24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 1, 3, 1]))
      + v4_25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 3, 2]))
      + v4_26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 1, 3, 4]))
      + v4_27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 0, 0, 4]))
      + v4_28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 0, 0, 0]))
      + v4_29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 0, 0, 1]))
      + v4_30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 0, 1]))
      + v4_31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 0, 4]))
      + v4_32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 0, 0]))
      + v4_33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 1, 0, 1]))
      + v4_34 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 0, 2]))
      + v4_35 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 1, 0, 4]))
      + v4_36 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 0, 3, 4]))
      + v4_37 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 0, 3, 0]))
      + v4_38 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 0, 3, 1]))
      + v4_39 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 3, 0]))
      + v4_40 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 4 t ![0, 1, 2, 1, 2])) :=
    stg4 P hsym (fun s => ∑ t : WZ, P t * G (step 4 t s))
  rw [h]
  simp only [sum_wz]
  rw [tr4_0_0, tr4_0_3, tr4_0_4, tr4_0_2, tr4_0_1, tr4_1_0, tr4_1_3, tr4_1_4, tr4_1_2, tr4_1_1, tr4_2_0, tr4_2_3, tr4_2_4, tr4_2_2, tr4_2_1, tr4_3_0, tr4_3_3, tr4_3_4, tr4_3_2, tr4_3_1, tr4_4_0, tr4_4_3, tr4_4_4, tr4_4_2, tr4_4_1, tr4_5_0, tr4_5_3, tr4_5_4, tr4_5_2, tr4_5_1, tr4_6_0, tr4_6_3, tr4_6_4, tr4_6_2, tr4_6_1, tr4_7_0, tr4_7_3, tr4_7_4, tr4_7_2, tr4_7_1, tr4_8_0, tr4_8_3, tr4_8_4, tr4_8_2, tr4_8_1, tr4_9_0, tr4_9_3, tr4_9_4, tr4_9_2, tr4_9_1, tr4_10_0, tr4_10_3, tr4_10_4, tr4_10_2, tr4_10_1, tr4_11_0, tr4_11_3, tr4_11_4, tr4_11_2, tr4_11_1, tr4_12_0, tr4_12_3, tr4_12_4, tr4_12_2, tr4_12_1, tr4_13_0, tr4_13_3, tr4_13_4, tr4_13_2, tr4_13_1, tr4_14_0, tr4_14_3, tr4_14_4, tr4_14_2, tr4_14_1, tr4_15_0, tr4_15_3, tr4_15_4, tr4_15_2, tr4_15_1, tr4_16_0, tr4_16_3, tr4_16_4, tr4_16_2, tr4_16_1, tr4_17_0, tr4_17_3, tr4_17_4, tr4_17_2, tr4_17_1, tr4_18_0, tr4_18_3, tr4_18_4, tr4_18_2, tr4_18_1, tr4_19_0, tr4_19_3, tr4_19_4, tr4_19_2, tr4_19_1, tr4_20_0, tr4_20_3, tr4_20_4, tr4_20_2, tr4_20_1, tr4_21_0, tr4_21_3, tr4_21_4, tr4_21_2, tr4_21_1, tr4_22_0, tr4_22_3, tr4_22_4, tr4_22_2, tr4_22_1, tr4_23_0, tr4_23_3, tr4_23_4, tr4_23_2, tr4_23_1, tr4_24_0, tr4_24_3, tr4_24_4, tr4_24_2, tr4_24_1, tr4_25_0, tr4_25_3, tr4_25_4, tr4_25_2, tr4_25_1, tr4_26_0, tr4_26_3, tr4_26_4, tr4_26_2, tr4_26_1, tr4_27_0, tr4_27_3, tr4_27_4, tr4_27_2, tr4_27_1, tr4_28_0, tr4_28_3, tr4_28_4, tr4_28_2, tr4_28_1, tr4_29_0, tr4_29_3, tr4_29_4, tr4_29_2, tr4_29_1, tr4_30_0, tr4_30_3, tr4_30_4, tr4_30_2, tr4_30_1, tr4_31_0, tr4_31_3, tr4_31_4, tr4_31_2, tr4_31_1, tr4_32_0, tr4_32_3, tr4_32_4, tr4_32_2, tr4_32_1, tr4_33_0, tr4_33_3, tr4_33_4, tr4_33_2, tr4_33_1, tr4_34_0, tr4_34_3, tr4_34_4, tr4_34_2, tr4_34_1, tr4_35_0, tr4_35_3, tr4_35_4, tr4_35_2, tr4_35_1, tr4_36_0, tr4_36_3, tr4_36_4, tr4_36_2, tr4_36_1, tr4_37_0, tr4_37_3, tr4_37_4, tr4_37_2, tr4_37_1, tr4_38_0, tr4_38_3, tr4_38_4, tr4_38_2, tr4_38_1, tr4_39_0, tr4_39_3, tr4_39_4, tr4_39_2, tr4_39_1, tr4_40_0, tr4_40_3, tr4_40_4, tr4_40_2, tr4_40_1, ← hsym]
  rw [q5_0, q5_1, q5_2, q5_3, q5_4, q5_5, q5_6, q5_7, q5_8, q5_9, q5_10, q5_11, q5_12, q5_13, q5_14, q5_15, q5_16, q5_17, q5_18, q5_19, q5_20, q5_21, q5_22, q5_23, q5_24, q5_25, q5_26, q5_27, q5_28, q5_29, q5_30, q5_31, q5_32, q5_33, q5_34, q5_35, q5_36, q5_37, q5_38, q5_39, q5_40]
  ring
private theorem stg6 (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (∑ t4 : WZ, P t4 * (∑ t5 : WZ, P t5 * (G (step 5 t5 (step 4 t4 (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))))))))
      = wF0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 0]
      + wF1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 0, 4]
      + wF2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 0]
      + wF3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 4]
      + wF4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 0, 2]
      + wF5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 4]
      + wF6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 0]
      + wF7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 0, 3, 3]
      + wF8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 2]
      + wF9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 4]
      + wF10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 2]
      + wF11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 4]
      + wF12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 3]
      + wF13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 3, 0]
      + wF14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 0, 2, 2, 0]
      + wF15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 1]
      + wF16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 1, 4]
      + wF17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 2]
      + wF18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 4]
      + wF19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 2, 1]
      + wF20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 4]
      + wF21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 1]
      + wF22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 3, 3]
      + wF23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 3]
      + wF24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 4]
      + wF25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 1]
      + wF26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 1]
      + wF27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 4]
      + wF28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 2]
      + wF29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 1, 2]
      + wF30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 0]
      + wF31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 4]
      + wF32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 0, 1]
      + wF33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 4]
      + wF34 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 1]
      + wF35 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 1, 0, 0]
      + wF36 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 0]
      + wF37 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 4]
      + wF38 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 1]
      + wF39 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 0, 2]
      + wF40 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 4]
      + wF41 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 0]
      + wF42 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 3]
      + wF43 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 1, 1]
      + wF44 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 3, 1]
      + wF45 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 0, 1, 4]
      + wF46 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G ![0, 1, 2, 3, 0] := by
  have h : (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (∑ t4 : WZ, P t4 * (∑ t5 : WZ, P t5 * (G (step 5 t5 (step 4 t4 (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit))))))))))))))
      = v5_0 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 0, 0, 0]))
      + v5_1 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 0, 0, 4]))
      + v5_2 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 0, 4]))
      + v5_3 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 0, 0]))
      + v5_4 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 0, 2]))
      + v5_5 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 0, 3, 0]))
      + v5_6 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 0, 3, 4]))
      + v5_7 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 3, 2]))
      + v5_8 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 3, 4]))
      + v5_9 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 3, 0]))
      + v5_10 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 2, 2]))
      + v5_11 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 2, 4]))
      + v5_12 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 2, 0]))
      + v5_13 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 0, 2, 3, 3]))
      + v5_14 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 1, 1, 1]))
      + v5_15 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 1, 1, 4]))
      + v5_16 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 2, 2]))
      + v5_17 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 2, 4]))
      + v5_18 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 2, 1]))
      + v5_19 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 1, 3, 1]))
      + v5_20 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 3, 4]))
      + v5_21 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 3, 1]))
      + v5_22 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 1, 3, 4]))
      + v5_23 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 3, 2]))
      + v5_24 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 1, 4]))
      + v5_25 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 1, 1]))
      + v5_26 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 1, 2]))
      + v5_27 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 3, 3]))
      + v5_28 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 0, 0, 0]))
      + v5_29 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 0, 0, 4]))
      + v5_30 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 0, 0, 1]))
      + v5_31 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 1, 0, 1]))
      + v5_32 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 0, 4]))
      + v5_33 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 0, 1]))
      + v5_34 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 1, 0, 4]))
      + v5_35 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 0, 2]))
      + v5_36 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 0, 0]))
      + v5_37 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 0, 3, 0]))
      + v5_38 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 0, 3, 4]))
      + v5_39 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 0, 3, 1]))
      + v5_40 (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * (∑ t : WZ, P t * G (step 5 t ![0, 1, 2, 3, 0])) :=
    stg5 P hsym (fun s => ∑ t : WZ, P t * G (step 5 t s))
  rw [h]
  simp only [sum_wz]
  rw [tr5_0_0, tr5_0_3, tr5_0_4, tr5_0_2, tr5_0_1, tr5_1_0, tr5_1_3, tr5_1_4, tr5_1_2, tr5_1_1, tr5_2_0, tr5_2_3, tr5_2_4, tr5_2_2, tr5_2_1, tr5_3_0, tr5_3_3, tr5_3_4, tr5_3_2, tr5_3_1, tr5_4_0, tr5_4_3, tr5_4_4, tr5_4_2, tr5_4_1, tr5_5_0, tr5_5_3, tr5_5_4, tr5_5_2, tr5_5_1, tr5_6_0, tr5_6_3, tr5_6_4, tr5_6_2, tr5_6_1, tr5_7_0, tr5_7_3, tr5_7_4, tr5_7_2, tr5_7_1, tr5_8_0, tr5_8_3, tr5_8_4, tr5_8_2, tr5_8_1, tr5_9_0, tr5_9_3, tr5_9_4, tr5_9_2, tr5_9_1, tr5_10_0, tr5_10_3, tr5_10_4, tr5_10_2, tr5_10_1, tr5_11_0, tr5_11_3, tr5_11_4, tr5_11_2, tr5_11_1, tr5_12_0, tr5_12_3, tr5_12_4, tr5_12_2, tr5_12_1, tr5_13_0, tr5_13_3, tr5_13_4, tr5_13_2, tr5_13_1, tr5_14_0, tr5_14_3, tr5_14_4, tr5_14_2, tr5_14_1, tr5_15_0, tr5_15_3, tr5_15_4, tr5_15_2, tr5_15_1, tr5_16_0, tr5_16_3, tr5_16_4, tr5_16_2, tr5_16_1, tr5_17_0, tr5_17_3, tr5_17_4, tr5_17_2, tr5_17_1, tr5_18_0, tr5_18_3, tr5_18_4, tr5_18_2, tr5_18_1, tr5_19_0, tr5_19_3, tr5_19_4, tr5_19_2, tr5_19_1, tr5_20_0, tr5_20_3, tr5_20_4, tr5_20_2, tr5_20_1, tr5_21_0, tr5_21_3, tr5_21_4, tr5_21_2, tr5_21_1, tr5_22_0, tr5_22_3, tr5_22_4, tr5_22_2, tr5_22_1, tr5_23_0, tr5_23_3, tr5_23_4, tr5_23_2, tr5_23_1, tr5_24_0, tr5_24_3, tr5_24_4, tr5_24_2, tr5_24_1, tr5_25_0, tr5_25_3, tr5_25_4, tr5_25_2, tr5_25_1, tr5_26_0, tr5_26_3, tr5_26_4, tr5_26_2, tr5_26_1, tr5_27_0, tr5_27_3, tr5_27_4, tr5_27_2, tr5_27_1, tr5_28_0, tr5_28_3, tr5_28_4, tr5_28_2, tr5_28_1, tr5_29_0, tr5_29_3, tr5_29_4, tr5_29_2, tr5_29_1, tr5_30_0, tr5_30_3, tr5_30_4, tr5_30_2, tr5_30_1, tr5_31_0, tr5_31_3, tr5_31_4, tr5_31_2, tr5_31_1, tr5_32_0, tr5_32_3, tr5_32_4, tr5_32_2, tr5_32_1, tr5_33_0, tr5_33_3, tr5_33_4, tr5_33_2, tr5_33_1, tr5_34_0, tr5_34_3, tr5_34_4, tr5_34_2, tr5_34_1, tr5_35_0, tr5_35_3, tr5_35_4, tr5_35_2, tr5_35_1, tr5_36_0, tr5_36_3, tr5_36_4, tr5_36_2, tr5_36_1, tr5_37_0, tr5_37_3, tr5_37_4, tr5_37_2, tr5_37_1, tr5_38_0, tr5_38_3, tr5_38_4, tr5_38_2, tr5_38_1, tr5_39_0, tr5_39_3, tr5_39_4, tr5_39_2, tr5_39_1, tr5_40_0, tr5_40_3, tr5_40_4, tr5_40_2, tr5_40_1, ← hsym]
  rw [q6_0, q6_1, q6_2, q6_3, q6_4, q6_5, q6_6, q6_7, q6_8, q6_9, q6_10, q6_11, q6_12, q6_13, q6_14, q6_15, q6_16, q6_17, q6_18, q6_19, q6_20, q6_21, q6_22, q6_23, q6_24, q6_25, q6_26, q6_27, q6_28, q6_29, q6_30, q6_31, q6_32, q6_33, q6_34, q6_35, q6_36, q6_37, q6_38, q6_39, q6_40, q6_41, q6_42, q6_43, q6_44, q6_45, q6_46]
  ring

end BunkbedTM

/-! ## The requested statement -/

open Bunkbed Bunkbed.Hyper Bunkbed.TM Finset in
/-- **Evaluating the transfer matrix.** Summing a level-configuration weight against any
function of the induced profile collapses from `5 ^ 6` configurations onto the 47 reachable
profiles, with the explicit degree-6 polynomial weights of `wFinal`. -/
theorem solution (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (G : St → ℚ) :
    (∑ t₀ : WZ, ∑ t₁ : WZ, ∑ t₂ : WZ, ∑ t₃ : WZ, ∑ t₄ : WZ, ∑ t₅ : WZ,
        (P t₀ * P t₁ * P t₂ * P t₃ * P t₄ * P t₅)
          * G (step 5 t₅ (step 4 t₄ (step 3 t₃ (step 2 t₂ (step 1 t₁ (step 0 t₀ stInit)))))))
      = ∑ j : Fin 47, wFinal j (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * G (stFinal j) := by
  rw [show
    (∑ t₀ : WZ, ∑ t₁ : WZ, ∑ t₂ : WZ, ∑ t₃ : WZ, ∑ t₄ : WZ, ∑ t₅ : WZ,
        (P t₀ * P t₁ * P t₂ * P t₃ * P t₄ * P t₅)
          * G (step 5 t₅ (step 4 t₄ (step 3 t₃ (step 2 t₂ (step 1 t₁ (step 0 t₀ stInit)))))))
      = (∑ t0 : WZ, P t0 * (∑ t1 : WZ, P t1 * (∑ t2 : WZ, P t2 * (∑ t3 : WZ, P t3 * (∑ t4 : WZ, P t4 * (∑ t5 : WZ, P t5 * (G (step 5 t5 (step 4 t4 (step 3 t3 (step 2 t2 (step 1 t1 (step 0 t0 (stInit)))))))))))))) from by simp only [Finset.mul_sum, mul_assoc]]
  rw [BunkbedTM.stg6 P hsym G]
  simp only [wFinal, stFinal, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.isValue]
  ring

#print axioms solution
