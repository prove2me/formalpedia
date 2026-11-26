-- Prove2me | solution 1 for FirstPassageLinearTransport.centralOrbitScale_ge_n_rpow_neg_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:11:27.573801+00:00
-- url     : https://prove2.me/submissions/13208d1c-62fd-4644-8c99-ff203de39184

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k M : ℕ} (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M) :
    (n : ℝ) ^ (-driftGap) ≤ centralOrbitScale k := by
  have hb := driftGap_pos
  have hkMR : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hExp : -driftGap * M ≤ -driftGap * k := by nlinarith
  have hScaleM :
      (2 : ℝ) ^ (-driftGap * M) ≤ centralOrbitScale k := by
    rw [centralOrbitScale_eq_two_rpow_neg_gap]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  have hnLowerNat : 2 ^ M ≤ n := (mem_dyadicShell.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hBase :
      (n : ℝ) ^ (-driftGap) ≤ ((2 : ℝ) ^ M) ^ (-driftGap) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnLower (by linarith)
  have hEq :
      ((2 : ℝ) ^ M) ^ (-driftGap) =
        (2 : ℝ) ^ (-driftGap * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hEq] at hBase
  exact hBase.trans hScaleM
end FirstPassageLinearTransport
