-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_nonlinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:17.813947+00:00
-- url     : https://prove2.me/submissions/9a30005b-b457-4a6b-ab8b-c924e61885b7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCountRate_pow_eq_exp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualCriticalEndpointInformation_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (hM : 1 ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp
          (-(OptimizedLinearPullback.psi D / 3) * M) := by
  let w := OptimizedLinearPullback.psi D / 3
  let E := Real.exp (w * M)
  have hE : 0 < E := Real.exp_pos _
  have hbase :=
    sourceEndpointBad_div_pow_le hS M hM E hE
  have hinfo :=
    actualCriticalEndpointInformation_le M hM
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M := hbase
    _ ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ *
          (9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) := by
      gcongr
    _ =
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp (-w * M) := by
      rw [oddCountRate_pow_eq_exp]
      unfold E w
      have hcombine :
          Real.exp
                (OptimizedLinearPullback.psi D / 3 * (M : ℝ)) ^ 2 *
              Real.exp
                (-OptimizedLinearPullback.psi D * (M : ℝ)) =
            Real.exp
              (-(OptimizedLinearPullback.psi D / 3 * (M : ℝ))) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [show
        C * Real.exp
              (OptimizedLinearPullback.psi D / 3 * (M : ℝ)) ^ 2 *
            Real.exp (-D * Real.log 3) *
            Real.exp (-OptimizedLinearPullback.psi D * (M : ℝ)) =
          C * Real.exp (-D * Real.log 3) *
            (Real.exp
                (OptimizedLinearPullback.psi D / 3 * (M : ℝ)) ^ 2 *
              Real.exp
                (-OptimizedLinearPullback.psi D * (M : ℝ))) by ring]
      rw [hcombine]
      rw [← Real.exp_neg]
      ring
    _ =
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp
          (-(OptimizedLinearPullback.psi D / 3) * M) := rfl
end CollatzEndpointTransport.FixedTotal
