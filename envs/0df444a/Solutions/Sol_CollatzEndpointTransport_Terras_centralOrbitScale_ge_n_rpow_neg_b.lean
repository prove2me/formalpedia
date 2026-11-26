-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.centralOrbitScale_ge_n_rpow_neg_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:58.158325+00:00
-- url     : https://prove2.me/submissions/b331a9d2-57ad-4fb8-b312-86ba06a0a02c

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
import Theorems.Thm_CollatzEndpointTransport_Terras_centralOrbitScale_eq_two_rpow_neg_b
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_bConst_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {n k M : ℕ}
    (hkM : k ≤ M)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1))) :
    (n : ℝ) ^ (-QuantitativeDensity.bConst) ≤
      centralOrbitScale k := by
  have hb : 0 < QuantitativeDensity.bConst :=
    QuantitativeDensity.bConst_pos
  have hkMR : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hExp :
      -QuantitativeDensity.bConst * M ≤
        -QuantitativeDensity.bConst * k := by
    nlinarith
  have hScaleM :
      (2 : ℝ) ^ (-QuantitativeDensity.bConst * M) ≤
        centralOrbitScale k := by
    rw [centralOrbitScale_eq_two_rpow_neg_b]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
  have hnLowerNat : 2 ^ M ≤ n := (Finset.mem_Ico.mp hnShell).1
  have hnLower : (2 : ℝ) ^ M ≤ n := by exact_mod_cast hnLowerNat
  have hBase :
      (n : ℝ) ^ (-QuantitativeDensity.bConst) ≤
        ((2 : ℝ) ^ M) ^ (-QuantitativeDensity.bConst) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hnLower (by linarith)
  have hEq :
      ((2 : ℝ) ^ M) ^ (-QuantitativeDensity.bConst) =
        (2 : ℝ) ^ (-QuantitativeDensity.bConst * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hEq] at hBase
  exact hBase.trans hScaleM
end CollatzEndpointTransport.Terras
